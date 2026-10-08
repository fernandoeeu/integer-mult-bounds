// PR 7 (jacklightChen): the "cancellation-free triple exclusion" producer of
// notes/prime-field28-construction.tex (paragraph "Cancellation-free triple
// exclusion"), used twice by PR 7: at n = 26 as the local producer of the F3
// five-subset bit network (one copy per common pair), and at n = 28 as the
// disjoint producer of the complex network ("Paired triple exclusion on the
// complex side").
//
// Problem. On n points, inputs x_T for the triples T. For every set E of at most
// three points, the sum of x_T over T disjoint from E. Nodes are formal sums
// identified by their support; additions join disjoint supports; equal supports
// are interned (the first decomposition is kept); unused nodes are removed.
//
// The note's prose fixes the algebra (pair the points, aggregate monomials by the
// pairs they touch, recurse; for E touching the pairs G start from the coarse sum
// avoiding G and add, for every nonempty set K of surviving partners, the
// contraction selecting exactly K: one point -> the repository's weighted
// paired-exclusion recursion, two points -> a weighted vector exclusion, three
// points -> one coefficient; direct sums at four or fewer points). It does not fix
// the summation orders, the order in which unused intermediate sums are created
// (which, with interning, decides which decomposition is kept), or the pairing of
// the contraction's own vertices. Those were taken from the PR's
// scripts/paired_triple_circuit.py and the repository's
// scripts/paired_exclusion_circuit.py (`block`, `vector`, `total`): balanced sums
// split at floor(k/2) with zero terms kept, prefix/suffix leave-one-out sums with
// every suffix created, and Python dict insertion order for every family of sums.
// This module is therefore a reimplementation of the PR's construction, not an
// independent reading of the prose (see REPORT, independence caveats). What is
// independent is the verification (`verifyPairedTriple`): supports are recomputed
// from the kept additions only and compared with the definition, every addition
// is checked disjoint, and the counts are taken from that pruned graph.

const ZERO_NODE = 0; // the empty sum; inputs are 1..V

export class SupportStore {
  readonly words: number;
  supports: Uint32Array[] = [new Uint32Array(0)];
  left: number[] = [0];
  right: number[] = [0];
  private byKey = new Map<string, number>();
  constructor(readonly inputs: number) {
    this.words = (inputs + 31) >>> 5;
    this.supports[0] = new Uint32Array(this.words);
    for (let k = 0; k < inputs; k++) {
      const s = new Uint32Array(this.words);
      s[k >>> 5]! |= 1 << (k & 31);
      this.supports.push(s);
      this.left.push(0);
      this.right.push(0);
      this.byKey.set(this.key(s), k + 1);
    }
  }
  private key(s: Uint32Array): string {
    let k = "";
    for (let i = 0; i < s.length; i++) k += String.fromCharCode(s[i]! & 0xffff, s[i]! >>> 16);
    return k;
  }
  get size() {
    return this.supports.length;
  }
  add(a: number, b: number): number {
    if (a === ZERO_NODE) return b;
    if (b === ZERO_NODE) return a;
    const sa = this.supports[a]!;
    const sb = this.supports[b]!;
    const u = new Uint32Array(this.words);
    for (let i = 0; i < this.words; i++) {
      if ((sa[i]! & sb[i]!) !== 0) throw new Error("addition of overlapping supports (cancellation)");
      u[i] = sa[i]! | sb[i]!;
    }
    const k = this.key(u);
    const found = this.byKey.get(k);
    if (found !== undefined) return found;
    const id = this.supports.length;
    this.supports.push(u);
    this.left.push(a);
    this.right.push(b);
    this.byKey.set(k, id);
    return id;
  }
  /** Balanced binary addition, split at floor(k/2), zero terms kept (left sum first). */
  total(vals: number[]): number {
    if (vals.length === 0) return ZERO_NODE;
    if (vals.length === 1) return vals[0]!;
    const m = vals.length >> 1;
    const l = this.total(vals.slice(0, m));
    const r = this.total(vals.slice(m));
    return this.add(l, r);
  }
  /** Prefix sums, all suffix sums, and the leave-one-out sums prefix[i] + suffix[i+1]. */
  leaveOneOut(vals: number[]): { total: number; leave: number[] } {
    const n = vals.length;
    const prefix = [ZERO_NODE];
    for (const x of vals) prefix.push(this.add(prefix[prefix.length - 1]!, x));
    const suffix = new Array<number>(n + 1).fill(ZERO_NODE);
    for (let i = n - 1; i >= 0; i--) suffix[i] = this.add(vals[i]!, suffix[i + 1]!);
    const leave: number[] = [];
    for (let i = 0; i < n; i++) leave.push(this.add(prefix[i]!, suffix[i + 1]!));
    return { total: prefix[n]!, leave };
  }
}

/** A weighted polynomial: monomials (sorted point lists) with node values, in insertion order. */
type Poly = { keys: number[][]; vals: number[]; index: Map<string, number> };
const K = (pts: readonly number[]) => pts.join(",");
function poly(): Poly {
  return { keys: [], vals: [], index: new Map() };
}
function push(p: Poly, key: number[], val: number) {
  p.index.set(K(key), p.keys.length);
  p.keys.push(key);
  p.vals.push(val);
}
const get = (p: Poly, key: number[]) => {
  const i = p.index.get(K(key));
  return i === undefined ? ZERO_NODE : p.vals[i]!;
};

/** Ordered subsets of `pts` of size at most k (by size, then lexicographic in list order). */
function subsetsUpTo(pts: number[], k: number): number[][] {
  const out: number[][] = [];
  const rec = (start: number, cur: number[], size: number) => {
    if (cur.length === size) {
      out.push([...cur]);
      return;
    }
    for (let i = start; i < pts.length; i++) {
      cur.push(pts[i]!);
      rec(i + 1, cur, size);
      cur.pop();
    }
  };
  for (let s = 0; s <= k; s++) rec(0, [], s);
  return out;
}
const pairsOf = (pts: number[]) => subsetsUpTo(pts, 2).filter((s) => s.length === 2);
const grouping = (pts: number[]) => {
  const g: number[][] = [];
  for (let i = 0; i < pts.length; i += 2) g.push(pts.slice(i, i + 2));
  return g;
};
const disjoint = (a: readonly number[], b: readonly number[]) => a.every((x) => !b.includes(x));

type BlockOut = { total: number; single: Map<number, number>; pair: Map<string, number>; pairOrder: number[][] };

export class PairedTripleBuilder {
  readonly st: SupportStore;
  readonly inputs: number[][];
  readonly outputs: Map<string, number> = new Map(); // key K(S) for every triple S
  readonly retainedTotal: number;
  constructor(readonly n: number, readonly base = 4) {
    const inputs: number[][] = [];
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) inputs.push([a, b, c]);
    this.inputs = inputs;
    this.st = new SupportStore(inputs.length);
    const w = poly();
    inputs.forEach((t, i) => push(w, t, i + 1));
    const all = [...Array(n).keys()];
    const res = this.triple(all, w);
    for (const t of inputs) this.outputs.set(K(t), res.get(K(t))!);
    // The PR retains the total (the output for E = {}) by re-running the producer on the same
    // store (scripts/prime_field_circuit.py, export_local); with interning this returns the
    // node already built for E = {} by the first run, which is what is used here.
    this.retainedTotal = res.get("")!;
  }

  /** Weighted graph exclusion of the repository (paired_exclusion_circuit.py `block`). */
  private block(points: number[], e: (a: number, b: number) => number, weights: Map<number, number>): BlockOut {
    const st = this.st;
    if (points.length <= 4) {
      const pairs = pairsOf(points);
      const tot = (omit: number[]) => st.total([...pairs.filter((p) => disjoint(p, omit)).map((p) => e(p[0]!, p[1]!)), ...points.filter((a) => !omit.includes(a)).map((a) => weights.get(a)!)]);
      const total = tot([]);
      const single = new Map<number, number>();
      for (const a of points) single.set(a, tot([a]));
      const pair = new Map<string, number>();
      for (const p of pairs) pair.set(K(p), tot(p));
      return { total, single, pair, pairOrder: pairs };
    }
    const groups = grouping(points);
    const ng = groups.length;
    const coarse = new Map<string, number>();
    for (const [i, j] of pairsOf([...Array(ng).keys()])) {
      const terms: number[] = [];
      for (const a of groups[i!]!) for (const b of groups[j!]!) terms.push(e(a, b));
      coarse.set(K([i!, j!]), st.total(terms));
    }
    const wt = new Map<number, number>();
    groups.forEach((g, i) => wt.set(i, st.total([...g.map((a) => weights.get(a)!), ...pairsOf(g).map((p) => e(p[0]!, p[1]!))])));
    const ce = (a: number, b: number) => coarse.get(a < b ? K([a, b]) : K([b, a]))!;
    const rec = this.block([...Array(ng).keys()], ce, wt);
    const strips = new Map<number, Map<number, number>>();
    const sums = new Map<number, number>();
    groups.forEach((g, i) => {
      const other = [...Array(ng).keys()].filter((j) => j !== i);
      for (const a of g) {
        const carry = st.total(g.filter((u) => u !== a).map((u) => weights.get(u)!));
        const vals = other.map((j) => {
          const terms: number[] = [];
          for (const u of g) if (u !== a) for (const v of groups[j]!) terms.push(e(u, v));
          return st.total(terms);
        });
        const r = st.leaveOneOut([carry, ...vals]);
        const m = new Map<number, number>();
        other.forEach((j, idx) => m.set(j, r.leave[idx + 1]!));
        strips.set(a, m);
        sums.set(a, r.total);
      }
    });
    const single = new Map<number, number>();
    groups.forEach((g, i) => g.forEach((a) => single.set(a, st.add(rec.single.get(i)!, sums.get(a)!))));
    const pair = new Map<string, number>();
    const pairOrder: number[][] = [];
    groups.forEach((g, i) => {
      for (const p of pairsOf(g)) {
        pair.set(K(p), rec.single.get(i)!);
        pairOrder.push(p);
      }
    });
    for (const [i, j] of pairsOf([...Array(ng).keys()])) {
      const gi = groups[i!]!;
      const gj = groups[j!]!;
      for (const a of gi) {
        const left = st.add(rec.pair.get(K([i!, j!]))!, strips.get(a)!.get(j!)!);
        for (const b of gj) {
          const terms: number[] = [];
          for (const u of gi) if (u !== a) for (const v of gj) if (v !== b) terms.push(e(u, v));
          const cross = st.total(terms);
          const inner = st.add(strips.get(b)!.get(i!)!, cross);
          pair.set(K([a, b]), st.add(left, inner));
          pairOrder.push([a, b]);
        }
      }
    }
    return { total: rec.total, single, pair, pairOrder };
  }

  /** Degree-three weighted exclusion (paired_triple_circuit.py `triple`). Keys of the result: K(E). */
  private triple(pts: number[], w: Poly): Map<string, number> {
    const st = this.st;
    const subsets = subsetsUpTo(pts, 3);
    const result = new Map<string, number>();
    if (pts.length <= this.base) {
      for (const s of subsets) result.set(K(s), st.total(w.keys.map((t, i) => (disjoint(s, t) ? w.vals[i]! : -1)).filter((x) => x !== -1)));
      return result;
    }
    const groups = grouping(pts);
    const ng = groups.length;
    const groupOf = new Map<number, number>();
    groups.forEach((g, i) => g.forEach((u) => groupOf.set(u, i)));
    const touched = (t: readonly number[]) => [...new Set(t.map((u) => groupOf.get(u)!))].sort((a, b) => a - b);

    // coarse polynomial on the group indices
    const parts = new Map<string, { key: number[]; xs: number[] }>();
    w.keys.forEach((t, i) => {
      const g = touched(t);
      const k = K(g);
      if (!parts.has(k)) parts.set(k, { key: g, xs: [] });
      parts.get(k)!.xs.push(w.vals[i]!);
    });
    const coarse = poly();
    for (const { key, xs } of parts.values()) push(coarse, key, st.total(xs));
    const outCoarse = this.triple([...Array(ng).keys()], coarse);

    // contract one surviving point
    const one = new Map<number, Map<string, number>>();
    for (const u of pts) {
      const g = groupOf.get(u)!;
      const others = [...Array(ng).keys()].filter((j) => j !== g);
      const pieces = new Map<string, { key: number[]; xs: number[] }>();
      w.keys.forEach((t, i) => {
        if (!t.includes(u)) return;
        const rest = t.filter((a) => a !== u);
        if (rest.some((a) => groupOf.get(a) === g)) return;
        const key = touched(rest);
        const k = K(key);
        if (!pieces.has(k)) pieces.set(k, { key, xs: [] });
        pieces.get(k)!.xs.push(w.vals[i]!);
      });
      const coeff = new Map<string, number>();
      for (const [k, { xs }] of pieces) coeff.set(k, st.total(xs));
      const cg = (key: number[]) => coeff.get(K(key)) ?? ZERO_NODE;
      const weights = new Map<number, number>();
      for (const j of others) weights.set(j, cg([j]));
      const b = this.block(others, (x, y) => cg(x < y ? [x, y] : [y, x]), weights);
      const c0 = cg([]);
      const m = new Map<string, number>();
      m.set("", st.add(c0, b.total));
      for (const [j, x] of b.single) m.set(K([j]), st.add(c0, x));
      for (const p of b.pairOrder) m.set(K(p), st.add(c0, b.pair.get(K(p))!));
      one.set(u, m);
    }

    // contract two surviving points (remaining degree at most one)
    const two = new Map<string, Map<string, number>>();
    for (const [u, v] of pairsOf(pts)) {
      const i = groupOf.get(u!)!;
      const j = groupOf.get(v!)!;
      if (i === j) continue;
      const others = [...Array(ng).keys()].filter((k) => k !== i && k !== j);
      const vals = others.map((k) => st.total(groups[k]!.map((a) => get(w, [u!, v!, a].sort((x, y) => x - y)))));
      const r = st.leaveOneOut([get(w, [u!, v!]), ...vals]);
      const m = new Map<string, number>();
      m.set("", r.total);
      others.forEach((k, idx) => m.set(K([k]), r.leave[idx + 1]!));
      two.set(K([u!, v!]), m);
    }

    for (const ex of subsets) {
      const G = touched(ex);
      const survivors: number[] = [];
      for (const i of G) for (const u of groups[i]!) if (!ex.includes(u)) survivors.push(u);
      if (survivors.length > 3) throw new Error("more than three survivors");
      const pieces = new Map<string, number>();
      pieces.set("", outCoarse.get(K(G))!);
      for (const u of survivors) pieces.set(K([u]), one.get(u)!.get(K(G.filter((i) => i !== groupOf.get(u))))!);
      for (const [u, v] of pairsOf(survivors)) {
        const m = two.get(K([u!, v!]));
        if (!m) throw new Error("two survivors in one group");
        pieces.set(K([u!, v!]), m.get(K(G.filter((i) => i !== groupOf.get(u!) && i !== groupOf.get(v!))))!);
      }
      let order: number[][];
      if (survivors.length === 3) {
        pieces.set(K(survivors), get(w, survivors));
        const [a, b, c] = survivors as [number, number, number];
        order = [[], [a], [b], [a, b], [c], [a, c], [b, c], [a, b, c]];
      } else order = subsetsUpTo(survivors, survivors.length);
      result.set(K(ex), st.total(order.map((s) => pieces.get(K(s))!)));
    }
    return result;
  }
}

export type PairedTripleReport = {
  n: number;
  inputs: number;
  outputs: number;
  additions: number; // reachable from the outputs
  retainedAdditions: number; // reachable from the outputs or the retained total
  byCore: Record<number, number>; // additions by |common points of the support| (reachable from the outputs)
  outputsExact: boolean; // every output = sum over triples disjoint from its triple
  totalExact: boolean; // the retained total = sum of all inputs
  allDisjoint: boolean;
  nonzeroCoefficients: number;
  created: number; // all nodes created by the builder (inputs and unused sums included)
};

/** The active subgraph, renumbered in creation (topological) order. */
export type ActiveGraph = {
  n: number;
  V: number;
  left: Int32Array; // per active addition: child ids (inputs 1..V, additions V+1..)
  right: Int32Array;
  outputs: Int32Array; // per triple (lexicographic): node id
  total: number; // the retained total
};

const pop32 = (x: number) => {
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
};

export function activeGraph(b: PairedTripleBuilder, withTotal: boolean): ActiveGraph {
  const st = b.st;
  const V = b.inputs.length;
  const used = new Uint8Array(st.size);
  const roots = b.inputs.map((t) => b.outputs.get(K(t))!);
  const stack = withTotal ? [...roots, b.retainedTotal] : [...roots];
  while (stack.length) {
    const x = stack.pop()!;
    if (x === ZERO_NODE || used[x]) continue;
    used[x] = 1;
    if (x > V) stack.push(st.left[x]!, st.right[x]!);
  }
  const renum = new Int32Array(st.size).fill(-1);
  for (let i = 0; i <= V; i++) renum[i] = i;
  const L: number[] = [];
  const R: number[] = [];
  for (let x = V + 1; x < st.size; x++) {
    if (!used[x]) continue;
    renum[x] = V + 1 + L.length;
    L.push(renum[st.left[x]!]!);
    R.push(renum[st.right[x]!]!);
  }
  return { n: b.n, V, left: Int32Array.from(L), right: Int32Array.from(R), outputs: Int32Array.from(roots.map((x) => renum[x]!)), total: renum[b.retainedTotal]! };
}

/**
 * Verification from the active graph alone: supports are recomputed from the kept additions,
 * every addition must join disjoint supports, every output must equal its definition.
 * Also the core histogram: |intersection of the triples of the support| for every addition.
 */
export function verifyPairedTriple(g: ActiveGraph, created = 0): PairedTripleReport & { core: Int32Array } {
  const { n, V } = g;
  const words = (V + 31) >>> 5;
  const nodes = V + 1 + g.left.length;
  const sup = new Uint32Array(nodes * words);
  const core = new Int32Array(nodes);
  const triples: number[][] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) triples.push([a, b, c]);
  for (let i = 0; i < V; i++) {
    sup[(i + 1) * words + (i >>> 5)]! |= 1 << (i & 31);
    core[i + 1] = triples[i]!.reduce((m, p) => m | (1 << p), 0);
  }
  let allDisjoint = true;
  for (let k = 0; k < g.left.length; k++) {
    const x = V + 1 + k;
    const a = g.left[k]!;
    const b = g.right[k]!;
    if (!(a > 0 && a < x && b > 0 && b < x)) throw new Error("not in topological order");
    for (let w = 0; w < words; w++) {
      const sa = sup[a * words + w]!;
      const sb = sup[b * words + w]!;
      if ((sa & sb) !== 0) allDisjoint = false;
      sup[x * words + w] = sa | sb;
    }
    core[x] = core[a]! & core[b]!;
  }
  const masks = triples.map((t) => t.reduce((m, p) => m | (1 << p), 0));
  let outputsExact = true;
  let nonzero = 0;
  g.outputs.forEach((node, t) => {
    const E = masks[t]!;
    for (let i = 0; i < V; i++) {
      const want = (masks[i]! & E) === 0;
      const has = ((sup[node * words + (i >>> 5)]! >>> (i & 31)) & 1) === 1;
      if (want !== has) outputsExact = false;
      if (has) nonzero++;
    }
  });
  let totalExact = true;
  for (let i = 0; i < V; i++) if (((sup[g.total * words + (i >>> 5)]! >>> (i & 31)) & 1) !== 1) totalExact = false;
  // reachability from the outputs only (the retained total may add ancestors)
  const used = new Uint8Array(nodes);
  const stack = Array.from(g.outputs);
  while (stack.length) {
    const x = stack.pop()!;
    if (used[x]) continue;
    used[x] = 1;
    if (x > V) stack.push(g.left[x - V - 1]!, g.right[x - V - 1]!);
  }
  let additions = 0;
  const byCore: Record<number, number> = {};
  for (let x = V + 1; x < nodes; x++)
    if (used[x]) {
      additions++;
      const c = pop32(core[x]!);
      byCore[c] = (byCore[c] ?? 0) + 1;
    }
  return { n, inputs: V, outputs: g.outputs.length, additions, retainedAdditions: g.left.length, byCore, outputsExact, totalExact, allDisjoint, nonzeroCoefficients: nonzero, created, core };
}

export function buildPairedTriple(n: number, withTotal: boolean) {
  const b = new PairedTripleBuilder(n);
  const g = activeGraph(b, withTotal);
  return { builder: b, graph: g, report: verifyPairedTriple(g, b.st.size - 1 - b.inputs.length) };
}
