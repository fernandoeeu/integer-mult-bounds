// PR 3 (eumemic): the compressed side circuit of the complex network at h = 25,
// rebuilt from notes/complex-circuit-construction.tex, subsections
// "Disjoint sums", "Pair stars" and "Injection rule", not from
// scripts/complex_circuit.py.
//
// Every node is a formal sum of inputs x_T (T a triple of [h]) identified by its
// support. Additions join disjoint supports. "Equal supports are identified
// within each of the two families below" (disjoint sums; pair stars), keeping
// the first decomposition, "and nodes that feed no injected piece are removed".
//
// Disjoint sums (exclusion sets E are bit masks over [h], |E| <= 3):
//   vec(list, k):   for every E of at most k of the list's points, the sum of the
//                   nodes whose points avoid E. Split at floor(n/2), recurse, and
//                   form each output by one addition left[E_L] + right[E_R].
//   pairs(X, w):    split X into halves L, R; recurse; vec on each cross row
//                   (w(u, r))_{r in R}; vec down the columns of the row outputs with
//                   the remaining budget; add the three regions.
//   tri(X):         halves L, R; P_r = pairs(L, x_{uvr}), P'_u = pairs(R, x_{uab});
//                   vec over r in R of P_r[E_L]; vec over u in L of P'_u[E_R];
//                   add the four regions (L, R, two in L one in R, one in L two in R).
// Top level: L = {0..11}, R = {12..24}; a target S receives tri(L)[S_L], tri(R)[S_R],
// the two vec outputs over R1 = {12..17}, R2 = {18..24} of P_r[S_L], and the two
// over L1 = {0..5}, L2 = {6..11} of P'_u[S_R].
//
// Pair stars: for a < b, the other points u_1 < ... < u_{h-2}; prefix sums pi_i,
// suffix sums sigma_i; target {a,b,u_i} receives pi_{i-1} and sigma_{i+1}.
//
// Injection rule: a piece whose triples cover every point outside S is replaced
// by its two summands, recursively.
//
// The prose leaves the order of the region additions open. `RegionOrder` makes it
// explicit; with interning it could change the count (it does not here: see tests).

import { tripleIndex, tripleList } from "../global";

const NONE = -1;
export type RegionOrder = "leftFold" | "rightFold";

/** Node store shared by both families; interning is per family. */
class Store {
  readonly words: number;
  supports: Uint32Array[] = [];
  left: number[] = []; // for every node; -1 for inputs
  right: number[] = [];
  family: number[] = []; // 0 input, 1 disjoint, 2 pair star
  private byKey: Map<string, number>[] = [new Map(), new Map(), new Map()];
  constructor(readonly inputs: number) {
    this.words = (inputs + 31) >>> 5;
    for (let k = 0; k < inputs; k++) {
      const s = new Uint32Array(this.words);
      s[k >>> 5]! |= 1 << (k & 31);
      this.supports.push(s);
      this.left.push(-1);
      this.right.push(-1);
      this.family.push(0);
    }
  }
  private key(s: Uint32Array): string {
    let k = "";
    for (let i = 0; i < s.length; i++) k += String.fromCharCode(s[i]! & 0xffff, s[i]! >>> 16);
    return k;
  }
  add(fam: 1 | 2, x: number, y: number): number {
    if (x === NONE) return y;
    if (y === NONE) return x;
    const sx = this.supports[x]!;
    const sy = this.supports[y]!;
    const u = new Uint32Array(this.words);
    for (let i = 0; i < this.words; i++) {
      if ((sx[i]! & sy[i]!) !== 0) throw new Error("addition of overlapping supports");
      u[i] = sx[i]! | sy[i]!;
    }
    const key = this.key(u);
    const found = this.byKey[fam]!.get(key);
    if (found !== undefined) return found;
    const id = this.supports.length;
    this.supports.push(u);
    this.left.push(x);
    this.right.push(y);
    this.family.push(fam);
    this.byKey[fam]!.set(key, id);
    return id;
  }
}

const popcount = (x: number) => {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
};

/** All masks of at most k points of `pts`. */
function subsets(pts: number[], k: number): number[] {
  const out = [0];
  const rec = (start: number, mask: number, size: number) => {
    for (let i = start; i < pts.length; i++) {
      const m = mask | (1 << pts[i]!);
      out.push(m);
      if (size + 1 < k) rec(i + 1, m, size + 1);
    }
  };
  if (k > 0) rec(0, 0, 0);
  return out;
}

export type Piece = { target: number; node: number; sign: 1 | -1 };

export type ComplexCircuit = {
  h: number;
  store: Store;
  pieces: Piece[]; // after the injection rule
  splitDisjoint: number; // pieces split by the rule
  splitStar: number;
  emptyPieces: number; // empty disjoint pieces (the note implies none)
  /** Only with `retain`: tri over all h points with exclusion budget 1, on the same store (PR 4 head 8c225e6). */
  retained?: Map<number, number>;
};

/**
 * A replacement disjoint producer (PR 7): an addition DAG on the triples of [h] in topological
 * order (inputs 1..V in lexicographic triple order, additions V+1..), and for every triple S
 * (lexicographic) the node whose support is every triple disjoint from S. Each target then
 * receives that one node (coefficient +1/2) instead of PR 3's six disjoint pieces.
 */
export type DisjointProducer = { V: number; left: Int32Array; right: Int32Array; outputs: Int32Array };

export function buildComplexCircuit(h = 25, order: RegionOrder = "leftFold", retain = false, producer?: DisjointProducer): ComplexCircuit {
  const triples = tripleList(h);
  const st = new Store(triples.length);
  const x = (a: number, b: number, c: number) => tripleIndex(h, [a, b, c]);
  const D = (p: number, q: number) => st.add(1, p, q);
  const sumRegions = (ns: number[]) =>
    order === "leftFold" ? ns.reduce((acc, n) => D(acc, n), NONE) : ns.reduceRight((acc, n) => D(n, acc), NONE);

  type Item = { p: number; node: number };
  function vec(items: Item[], k: number): Map<number, number> {
    const out = new Map<number, number>();
    if (items.length === 0) {
      out.set(0, NONE);
      return out;
    }
    if (items.length === 1) {
      out.set(0, items[0]!.node);
      if (k >= 1) out.set(1 << items[0]!.p, NONE);
      return out;
    }
    const mid = items.length >> 1;
    const L = vec(items.slice(0, mid), k);
    const R = vec(items.slice(mid), k);
    for (const [eL, nL] of L) for (const [eR, nR] of R) if (popcount(eL) + popcount(eR) <= k) out.set(eL | eR, D(nL, nR));
    return out;
  }

  function pairs(X: number[], w: (u: number, v: number) => number, k: number): Map<number, number> {
    if (X.length <= 1) {
      const out = new Map<number, number>();
      for (const E of subsets(X, k)) out.set(E, NONE);
      return out;
    }
    const mid = X.length >> 1;
    const Lp = X.slice(0, mid);
    const Rp = X.slice(mid);
    const PL = pairs(Lp, w, k);
    const PR = pairs(Rp, w, k);
    const rows = new Map<number, Map<number, number>>();
    for (const u of Lp) rows.set(u, vec(Rp.map((r) => ({ p: r, node: w(u, r) })), k));
    const cross = new Map<number, number>();
    for (const eR of subsets(Rp, k)) {
      const col = vec(Lp.map((u) => ({ p: u, node: rows.get(u)!.get(eR)! })), k - popcount(eR));
      for (const [eL, n] of col) cross.set(eL | eR, n);
    }
    const out = new Map<number, number>();
    for (const [eL, nL] of PL) for (const [eR, nR] of PR) if (popcount(eL) + popcount(eR) <= k) out.set(eL | eR, sumRegions([nL, nR, cross.get(eL | eR)!]));
    return out;
  }

  /** The two cross regions of tri(X) at top level are needed per half; this returns the families. */
  function crossFamilies(Lp: number[], Rp: number[], k: number) {
    const P = new Map<number, Map<number, number>>(); // r -> pairs(L, x_{uvr})
    for (const r of Rp) P.set(r, pairs(Lp, (u, v) => x(u, v, r), k));
    const Pp = new Map<number, Map<number, number>>(); // u -> pairs(R, x_{uab})
    for (const u of Lp) Pp.set(u, pairs(Rp, (a, b) => x(u, a, b), k));
    return { P, Pp };
  }

  function tri(X: number[], k: number): Map<number, number> {
    const out = new Map<number, number>();
    if (X.length <= 2) {
      for (const E of subsets(X, k)) out.set(E, NONE);
      return out;
    }
    const mid = X.length >> 1;
    const Lp = X.slice(0, mid);
    const Rp = X.slice(mid);
    const TL = tri(Lp, k);
    const TR = tri(Rp, k);
    const { P, Pp } = crossFamilies(Lp, Rp, k);
    const r21 = new Map<number, number>();
    for (const eL of subsets(Lp, k)) {
      const v = vec(Rp.map((r) => ({ p: r, node: P.get(r)!.get(eL)! })), k - popcount(eL));
      for (const [eR, n] of v) r21.set(eL | eR, n);
    }
    const r12 = new Map<number, number>();
    for (const eR of subsets(Rp, k)) {
      const v = vec(Lp.map((u) => ({ p: u, node: Pp.get(u)!.get(eR)! })), k - popcount(eR));
      for (const [eL, n] of v) r12.set(eL | eR, n);
    }
    for (const [eL, nL] of TL) for (const [eR, nR] of TR) if (popcount(eL) + popcount(eR) <= k) out.set(eL | eR, sumRegions([nL, nR, r21.get(eL | eR)!, r12.get(eL | eR)!]));
    return out;
  }

  const all = [...Array(h).keys()];
  const raw: Piece[] = [];
  const maskOf = (pts: number[]) => pts.reduce((m, p) => m | (1 << p), 0);
  if (producer) {
    // PR 7: transfer the producer's additions into the disjoint family, in creation order
    // (paired_complex.py: nodes added for sorted(paired.active) with interning per family).
    if (producer.V !== triples.length) throw new Error("producer on a different ground size");
    const map = new Int32Array(producer.V + 1 + producer.left.length);
    for (let i = 1; i <= producer.V; i++) map[i] = i - 1;
    for (let k = 0; k < producer.left.length; k++) map[producer.V + 1 + k] = D(map[producer.left[k]!]!, map[producer.right[k]!]!);
    for (let t = 0; t < triples.length; t++) raw.push({ target: t, node: map[producer.outputs[t]!]!, sign: 1 });
  } else {
    // ---- top level
    const mid = h >> 1;
    const Lp = all.slice(0, mid);
    const Rp = all.slice(mid);
    const TL = tri(Lp, 3);
    const TR = tri(Rp, 3);
    const { P, Pp } = crossFamilies(Lp, Rp, 3);
    const R1 = Rp.slice(0, Rp.length >> 1);
    const R2 = Rp.slice(Rp.length >> 1);
    const L1 = Lp.slice(0, Lp.length >> 1);
    const L2 = Lp.slice(Lp.length >> 1);
    const halfVec = new Map<string, Map<number, number>>();
    const half = (tag: string, pts: number[], fam: Map<number, Map<number, number>>, e: number) => {
      const key = `${tag}:${e}`;
      if (!halfVec.has(key)) halfVec.set(key, vec(pts.map((p) => ({ p, node: fam.get(p)!.get(e)! })), 3 - popcount(e)));
      return halfVec.get(key)!;
    };

    const Lmask = Lp.reduce((m, p) => m | (1 << p), 0);
    const Rmask = Rp.reduce((m, p) => m | (1 << p), 0);
    const R1m = maskOf(R1);
    const R2m = maskOf(R2);
    const L1m = maskOf(L1);
    const L2m = maskOf(L2);
    for (let t = 0; t < triples.length; t++) {
      const S = maskOf(triples[t]!);
      const SL = S & Lmask;
      const SR = S & Rmask;
      const ds = [
        TL.get(SL)!,
        TR.get(SR)!,
        half("R1", R1, P, SL).get(SR & R1m),
        half("R2", R2, P, SL).get(SR & R2m),
        half("L1", L1, Pp, SR).get(SL & L1m),
        half("L2", L2, Pp, SR).get(SL & L2m),
      ];
      for (const n of ds) raw.push({ target: t, node: n === undefined ? NONE : n, sign: 1 });
    }
  }

  // ---- pair stars
  const S2 = (p: number, q: number) => st.add(2, p, q);
  for (let a = 0; a < h; a++)
    for (let b = a + 1; b < h; b++) {
      const u = all.filter((z) => z !== a && z !== b);
      const n = u.length;
      const pi: number[] = new Array(n + 1).fill(NONE); // pi[i], i = 1..n
      for (let i = 1; i <= n; i++) pi[i] = S2(pi[i - 1]!, x(a, b, u[i - 1]!));
      const sg: number[] = new Array(n + 2).fill(NONE); // sigma[i], i = 1..n
      for (let i = n; i >= 1; i--) sg[i] = S2(x(a, b, u[i - 1]!), sg[i + 1]!);
      for (let i = 1; i <= n; i++) {
        const t = tripleIndex(h, [a, b, u[i - 1]!]);
        raw.push({ target: t, node: pi[i - 1]!, sign: -1 });
        raw.push({ target: t, node: sg[i + 1]!, sign: -1 });
      }
    }

  // ---- injection rule
  const pointsOf = (node: number): number => {
    const s = st.supports[node]!;
    let m = 0;
    for (let k = 0; k < triples.length; k++) if ((s[k >>> 5]! >>> (k & 31)) & 1) m |= maskOf(triples[k]!);
    return m;
  };
  const full = (1 << h) - 1;
  const pieces: Piece[] = [];
  let splitDisjoint = 0;
  let splitStar = 0;
  let emptyPieces = 0;
  const inject = (p: Piece) => {
    if (p.node === NONE) return;
    const S = maskOf(triples[p.target]!);
    const outside = full & ~S;
    if ((pointsOf(p.node) & outside) === outside) {
      if (st.left[p.node]! < 0) throw new Error("a single triple cannot cover every outside point");
      if (p.sign === 1) splitDisjoint++;
      else splitStar++;
      inject({ ...p, node: st.left[p.node]! });
      inject({ ...p, node: st.right[p.node]! });
      return;
    }
    pieces.push(p);
  };
  for (const p of raw) {
    // pi_0 and sigma_{h-1} are empty by definition; an empty disjoint piece is counted
    if (p.node === NONE) {
      if (p.sign === 1) emptyPieces++;
      continue;
    }
    inject(p);
  }
  // PR 4 (head 8c225e6) retains the exclusion totals E_i (i < h-1) and C_* as the outputs of
  // "source.tri(list(range(h)), 1)" on PR 3's builder, i.e. tri over all points with budget 1,
  // evaluated after the pieces on the same store (equal supports reuse existing nodes).
  // Off by default; nothing else in this function depends on it.
  const retained = retain ? tri(all, 1) : undefined;
  return { h, store: st, pieces, splitDisjoint, splitStar, emptyPieces, retained };
}

export type ComplexReport = {
  inputs: number;
  additions: number; // after removing nodes that feed no injected piece
  disjointAdditions: number;
  starAdditions: number;
  injections: number;
  piecesPerTarget: { min: number; max: number };
  splitDisjoint: number;
  splitStar: number;
  emptyPieces: number;
  inputsUsed: number;
  nonzeroCoefficients: number;
  sideMapExact: boolean; // +1/2 on disjoint triples, -1/2 on intersection two, 0 elsewhere, each exactly once
  allAdditionsDisjoint: boolean;
  piecesMeetTargetEvenly: boolean; // every triple of every piece meets S in 0 or 2 points
};

/**
 * Prune and verify. Supports are recomputed from the kept addition list only
 * (not taken from the builder), then compared with the side map
 * (1/2) sum_{T cap S = empty} x_T - (1/2) sum_{|T cap S| = 2} x_T for every target S.
 */
export function verifyComplexCircuit(c: ComplexCircuit): ComplexReport {
  const { store: st, h } = c;
  const triples = tripleList(h);
  const V = triples.length;
  const total = st.supports.length;
  const used = new Uint8Array(total);
  const stack = c.pieces.map((p) => p.node);
  while (stack.length) {
    const n = stack.pop()!;
    if (used[n]) continue;
    used[n] = 1;
    if (st.left[n]! >= 0) stack.push(st.left[n]!, st.right[n]!);
  }
  let additions = 0;
  let disjointAdditions = 0;
  let starAdditions = 0;
  let inputsUsed = 0;
  for (let n = 0; n < total; n++) {
    if (!used[n]) continue;
    if (st.family[n] === 0) inputsUsed++;
    else {
      additions++;
      if (st.family[n] === 1) disjointAdditions++;
      else starAdditions++;
    }
  }
  // recompute supports of kept nodes from the kept additions (creation order is topological)
  const words = (V + 31) >>> 5;
  const sup = new Map<number, Uint32Array>();
  let disjoint = true;
  for (let n = 0; n < total; n++) {
    if (!used[n]) continue;
    const s = new Uint32Array(words);
    if (st.left[n]! < 0) s[n >>> 5]! |= 1 << (n & 31);
    else {
      const l = sup.get(st.left[n]!)!;
      const r = sup.get(st.right[n]!)!;
      for (let w = 0; w < words; w++) {
        if ((l[w]! & r[w]!) !== 0) disjoint = false;
        s[w] = l[w]! | r[w]!;
      }
    }
    sup.set(n, s);
  }
  const masks = triples.map((t) => t.reduce((m, p) => m | (1 << p), 0));
  const byTarget: { node: number; sign: number }[][] = Array.from({ length: V }, () => []);
  for (const p of c.pieces) byTarget[p.target]!.push(p);
  let exact = true;
  let even = true;
  let nonzero = 0;
  let minP = Infinity;
  let maxP = 0;
  const coef = new Int8Array(V);
  for (let t = 0; t < V; t++) {
    coef.fill(0);
    const S = masks[t]!;
    const ps = byTarget[t]!;
    minP = Math.min(minP, ps.length);
    maxP = Math.max(maxP, ps.length);
    for (const p of ps) {
      const s = sup.get(p.node)!;
      for (let k = 0; k < V; k++)
        if ((s[k >>> 5]! >>> (k & 31)) & 1) {
          if (coef[k] !== 0) exact = false; // a triple covered twice
          coef[k] = p.sign;
          const meet = popcount(masks[k]! & S);
          if (meet !== 0 && meet !== 2) even = false;
        }
    }
    for (let k = 0; k < V; k++) {
      const meet = popcount(masks[k]! & S);
      const want = meet === 0 ? 1 : meet === 2 ? -1 : 0;
      if (coef[k] !== want) exact = false;
      if (coef[k] !== 0) nonzero++;
    }
  }
  return {
    inputs: V,
    additions,
    disjointAdditions,
    starAdditions,
    injections: c.pieces.length,
    piecesPerTarget: { min: minP, max: maxP },
    splitDisjoint: c.splitDisjoint,
    splitStar: c.splitStar,
    emptyPieces: c.emptyPieces,
    inputsUsed,
    nonzeroCoefficients: nonzero,
    sideMapExact: exact,
    allAdditionsDisjoint: disjoint,
    piecesMeetTargetEvenly: even,
  };
}
