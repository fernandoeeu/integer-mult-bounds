// PR 6 (eumemic): the aligned bit circuit with shared pair-star chains and group
// totals, rebuilt from notes/aligned-bit-construction.tex (prs/6, head 5015011),
// sections "Aligned blocks", "Shared pair-star sums" and "Totals", not from
// scripts/bit_circuit.py.
//
// The local algebra is the paired weighted recursion of src/circuit.ts (same
// conventions, same interning, same balanced sums); it is re-implemented here
// with three generalisations, so that src/circuit.ts stays unchanged:
//
//  1. Root blocks per group ("Aligned blocks"): for common point i, the ground
//     points 2k, 2k+1 form one block whenever both differ from i; the partner
//     i' = i XOR 1 is a singleton, kept at its own position k_i = floor(i/2).
//     Coarser levels group the block indices 2k, 2k+1 consecutively ("in the
//     same way"; there is no hole above the root), last one single.
//  2. Shared top-level chains ("Shared pair-star sums"): at the root, a vertex a
//     with partner q needs Y_i(a, J) = sum of x_{iqc}, c not in A or J. Let C be
//     the blocks other than A and the singleton {i'}. Prefix and suffix chains of
//     the block sums sum_{c in C} x_{iqc} in increasing block order; for J in C,
//     Y = (prefix before J + suffix after J) + x_{iqi'}; for J = {i'}, Y = the full
//     chain. The order of the final addition is not written in the note;
//     `starTripleLast` makes it explicit.
//  3. Totals ("Totals"): z_i = sum over all triples containing i, "the top-level
//     total of its recursion". The note does not write its summation order. Two
//     readings are offered: "base" sums every weight and edge of the coarsest
//     graph (at most four vertices) by the same balanced addition as the base
//     case; "none" omits the totals (for the comparison count only).
//
// Merging across groups is the rule of src/global.ts / src/prs/aligned.ts: a node
// whose triples all contain a second point j is keyed by the pair {i, j} and its
// set of third points; the first decomposition is kept, in common-point then
// local-node order. Afterwards nodes that no partial output and no total reaches
// are removed.

import { type Circuit, type Conventions, PUBLISHED_CONVENTIONS, pairIndex, pruneUnused } from "../circuit";
import { supportsOf } from "../verifyCircuit";
import { tripleIndex, tripleList } from "../global";
import { standardLabelling, verifyMerged, type MergedGraph } from "./aligned";

const NONE = -1;

export type BitCircuitOptions = {
  conv: Conventions;
  /** "aligned": PR 6's root blocks; "consecutive": the published blocks of src/circuit.ts (for the regression test). */
  rootBlocks: "aligned" | "consecutive";
  /** PR 6's shared top-level pair-star chains (true) or the original leave-one-out H (false). */
  sharedStars: boolean;
  /** In Y_i(a, J) for J in C: (prefix + suffix) + x_{iqi'} (true) or prefix + (suffix + x_{iqi'}) (false). */
  starTripleLast: boolean;
  totals: "base" | "none";
};

/**
 * The summation conventions that reproduce PR 6's stated c = 435346: floor split, zero terms
 * DROPPED before the split, edges before weights in the base sums. They were identified by
 * reading scripts/bit_circuit.py (its total() filters zeros) after the published conventions
 * gave 435344 (see README "Conventions" and prs/REPORT.md). The note says only that "the rest
 * of the recursion is unchanged"; with PUBLISHED_CONVENTIONS (zeros kept) the count is 435344.
 */
export const PR6_CONVENTIONS: Conventions = { split: "floor", zerosTakePart: false, baseWeightsFirst: false };
export const PR6_OPTIONS: BitCircuitOptions = { conv: PR6_CONVENTIONS, rootBlocks: "aligned", sharedStars: true, starTripleLast: true, totals: "base" };

function keyOf(s: Uint32Array): string {
  let k = "";
  for (let i = 0; i < s.length; i++) k += String.fromCharCode(s[i]! & 0xffff, s[i]! >>> 16);
  return k;
}

/** Local circuit of group i (local vertex u = ground point u < i ? u : u + 1). outputs[P] is the total (or -1). */
export function buildGroupCircuit(h: number, i: number, opt: BitCircuitOptions): Circuit & { total: number } {
  const n = h - 1;
  const conv = opt.conv;
  const P = (n * (n - 1)) / 2;
  const Wd = (P + 31) >>> 5;
  const supports: Uint32Array[] = [];
  const left: number[] = [];
  const right: number[] = [];
  const byKey = new Map<string, number>();
  for (let k = 0; k < P; k++) {
    const s = new Uint32Array(Wd);
    s[k >>> 5]! |= 1 << (k & 31);
    supports.push(s);
    byKey.set(keyOf(s), k);
  }
  function add(x: number, y: number): number {
    if (x === NONE) return y;
    if (y === NONE) return x;
    const sx = supports[x]!;
    const sy = supports[y]!;
    const u = new Uint32Array(Wd);
    for (let w = 0; w < Wd; w++) {
      if ((sx[w]! & sy[w]!) !== 0) throw new Error("addition of overlapping supports");
      u[w] = sx[w]! | sy[w]!;
    }
    const key = keyOf(u);
    const found = byKey.get(key);
    if (found !== undefined) return found;
    const id = supports.length;
    supports.push(u);
    left.push(x);
    right.push(y);
    byKey.set(key, id);
    return id;
  }
  function sumTerms(terms: number[]): number {
    const t = conv.zerosTakePart ? terms : terms.filter((x) => x !== NONE);
    if (t.length === 0) return NONE;
    if (t.length === 1) return t[0]!;
    const mid = conv.split === "floor" ? t.length >> 1 : (t.length + 1) >> 1;
    return add(sumTerms(t.slice(0, mid)), sumTerms(t.slice(mid)));
  }

  type Level = { O: number[]; F: number[][]; total: number };
  const local = (p: number) => (p < i ? p : p - 1);

  function solve(k: number, w: number[], e: number[][], given: number[][] | null, root: boolean): Level {
    const F: number[][] = Array.from({ length: k }, () => new Array<number>(k).fill(NONE));
    const all = [...Array(k).keys()];
    if (k <= 4) {
      const survivors = (deleted: number[]) => {
        const alive = all.filter((u) => !deleted.includes(u));
        const ws = alive.map((u) => w[u]!);
        const es: number[] = [];
        for (const u of alive) for (const v of alive) if (u < v) es.push(e[u]![v]!);
        return sumTerms(conv.baseWeightsFirst ? [...ws, ...es] : [...es, ...ws]);
      };
      const O = all.map((u) => survivors([u]));
      for (let u = 0; u < k; u++) for (let v = u + 1; v < k; v++) F[u]![v] = F[v]![u] = survivors([u, v]);
      return { O, F, total: opt.totals === "base" ? survivors([]) : NONE };
    }
    const blocks: number[][] = given ?? [];
    if (!given) for (let u = 0; u < k; u += 2) blocks.push(u + 1 < k ? [u, u + 1] : [u]);
    const K = blocks.length;
    const blockIdx = new Int32Array(k);
    blocks.forEach((A, j) => A.forEach((u) => (blockIdx[u] = j)));
    const blockOf = (u: number) => blockIdx[u]!;
    const partner = (u: number) => {
      const A = blocks[blockOf(u)]!;
      return A.length === 2 ? (A[0] === u ? A[1]! : A[0]!) : NONE;
    };
    const wCoarse = blocks.map((A) => sumTerms([...A.map((u) => w[u]!), ...(A.length === 2 ? [e[A[0]!]![A[1]!]!] : [])]));
    const eCoarse: number[][] = Array.from({ length: K }, () => new Array<number>(K).fill(NONE));
    for (let A = 0; A < K; A++)
      for (let B = A + 1; B < K; B++) {
        const terms: number[] = [];
        for (const u of blocks[A]!) for (const v of blocks[B]!) terms.push(e[u]![v]!);
        eCoarse[A]![B] = eCoarse[B]![A] = sumTerms(terms);
      }
    const coarse = solve(K, wCoarse, eCoarse, null, false);

    const Hleave: number[][] = Array.from({ length: k }, () => new Array<number>(K).fill(NONE));
    const Htotal = new Array<number>(k).fill(NONE);
    const singleton = blocks.findIndex((A) => A.length === 1);
    for (let a = 0; a < k; a++) {
      const A = blockOf(a);
      const ap = partner(a);
      if (root && opt.sharedStars) {
        if (ap === NONE) continue; // the singleton i': every Y is empty (w = 0 at the root)
        const chain = [...Array(K).keys()].filter((C) => C !== A && C !== singleton);
        const vec = chain.map((C) => sumTerms(blocks[C]!.map((v) => e[ap]![v]!)));
        const r = vec.length;
        const prefix = new Array<number>(r + 1).fill(NONE); // prefix[j] = vec[0..j-1]
        for (let j = 1; j <= r; j++) prefix[j] = add(prefix[j - 1]!, vec[j - 1]!);
        const suffix = new Array<number>(r + 2).fill(NONE); // suffix[j] = vec[j-1..r-1]
        for (let j = r; j >= 2; j--) suffix[j] = add(vec[j - 1]!, suffix[j + 1]!);
        const extra = singleton >= 0 ? e[ap]![blocks[singleton]![0]!]! : NONE; // x_{i q i'}
        chain.forEach((C, j0) => {
          const j = j0 + 1;
          Hleave[a]![C] = opt.starTripleLast ? add(add(prefix[j - 1]!, suffix[j + 1]!), extra) : add(prefix[j - 1]!, add(suffix[j + 1]!, extra));
        });
        if (singleton >= 0) Hleave[a]![singleton] = prefix[r]!;
        continue;
      }
      const others = [...Array(K).keys()].filter((C) => C !== A);
      const vec = [ap === NONE ? NONE : w[ap]!, ...others.map((C) => (ap === NONE ? NONE : sumTerms(blocks[C]!.map((v) => e[ap]![v]!))))];
      const r = vec.length - 1;
      const prefix = new Array<number>(r + 1);
      prefix[0] = vec[0]!;
      for (let j = 1; j <= r; j++) prefix[j] = add(prefix[j - 1]!, vec[j]!);
      const suffix = new Array<number>(r + 2).fill(NONE);
      for (let j = r; j >= 2; j--) suffix[j] = add(vec[j]!, suffix[j + 1]!);
      for (let j = 1; j <= r; j++) Hleave[a]![others[j - 1]!] = add(prefix[j - 1]!, suffix[j + 1]!);
      Htotal[a] = prefix[r]!;
    }
    for (const A of blocks) if (A.length === 2) F[A[0]!]![A[1]!] = F[A[1]!]![A[0]!] = coarse.O[blockOf(A[0]!)]!;
    for (let a = 0; a < k; a++)
      for (let b = a + 1; b < k; b++) {
        const A = blockOf(a);
        const B = blockOf(b);
        if (A === B) continue;
        const ap = partner(a);
        const bp = partner(b);
        const cross = ap === NONE || bp === NONE ? NONE : e[ap]![bp]!;
        F[a]![b] = F[b]![a] = add(add(coarse.F[A]![B]!, Hleave[a]![B]!), add(Hleave[b]![A]!, cross));
      }
    const O = root ? all.map(() => NONE) : all.map((a) => add(coarse.O[blockOf(a)]!, Htotal[a]!));
    return { O, F, total: coarse.total };
  }

  let rootBlocks: number[][] | null = null;
  if (opt.rootBlocks === "aligned") {
    if (h % 2 !== 0) throw new Error("aligned blocks need even h");
    rootBlocks = [];
    for (let k = 0; k < h / 2; k++) rootBlocks.push(k === i >> 1 ? [local(i ^ 1)] : [local(2 * k), local(2 * k + 1)]);
  }
  const e0: number[][] = Array.from({ length: n }, (_, a) => Array.from({ length: n }, (_, b) => (a === b ? NONE : pairIndex(n, a, b))));
  const res = solve(n, new Array<number>(n).fill(NONE), e0, rootBlocks, true);
  const outputs = new Int32Array(P + 1);
  for (let c = 0; c < n; c++) for (let d = c + 1; d < n; d++) outputs[pairIndex(n, c, d)] = res.F[c]![d]!;
  outputs[P] = res.total;
  const pruned = pruneUnused({ n, inputs: P, left, right, outputs: opt.totals === "base" ? outputs : outputs.slice(0, P) });
  return { ...pruned, total: opt.totals === "base" ? pruned.outputs[P]! : NONE };
}

export type AlignedBitGraph = MergedGraph & { totals: Int32Array; localAdditions: number[] };

/** Merge the h group circuits (keys as in src/global.ts), then prune. */
export function mergeGroups(h: number, opt: BitCircuitOptions): AlignedBitGraph {
  const n = h - 1;
  const P = (n * (n - 1)) / 2;
  const L = standardLabelling(h);
  const T = tripleList(h).length;
  const Wd = (P + 31) >>> 5;
  const pairs: [number, number][] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) pairs[pairIndex(n, a, b)] = [a, b];
  // vertex masks: pairs containing u
  const vmask = Array.from({ length: n }, (_, u) => {
    const m = new Uint32Array(Wd);
    for (let k = 0; k < P; k++) if (pairs[k]![0] === u || pairs[k]![1] === u) m[k >>> 5]! |= 1 << (k & 31);
    return m;
  });
  const left: number[] = [];
  const right: number[] = [];
  const byKey = new Map<string, number>();
  let merged = 0;
  const outputs = new Int32Array(h * P);
  const totals = new Int32Array(h).fill(-1);
  const localAdditions: number[] = [];
  for (let i = 0; i < h; i++) {
    const c = buildGroupCircuit(h, i, opt);
    localAdditions.push(c.left.length);
    const s = supportsOf(c);
    const g = (u: number) => L[i]![u]!;
    const map = new Int32Array(P + c.left.length);
    for (let k = 0; k < P; k++) map[k] = tripleIndex(h, [i, g(pairs[k]![0]), g(pairs[k]![1])]);
    for (let k = 0; k < c.left.length; k++) {
      const id = P + k;
      const sup = s[id]!;
      let key = `L${i}:${k}`;
      // common local vertex: the support lies inside the pairs containing u
      let first = -1;
      for (let w = 0; w < Wd && first < 0; w++) if (sup[w]) first = (w << 5) + (31 - Math.clz32(sup[w]! & -sup[w]!));
      for (const u of pairs[first]!) {
        const m = vmask[u]!;
        let inside = true;
        for (let w = 0; w < Wd && inside; w++) if ((sup[w]! & ~m[w]!) !== 0) inside = false;
        if (!inside) continue;
        const j = g(u);
        let mask = 0n;
        for (let w = 0; w < Wd; w++) {
          let x = sup[w]!;
          while (x) {
            const b = 31 - Math.clz32(x & -x);
            x &= x - 1;
            const [p0, p1] = pairs[(w << 5) + b]!;
            mask |= 1n << BigInt(g(p0 === u ? p1 : p0));
          }
        }
        key = `P${Math.min(i, j)},${Math.max(i, j)}:${mask.toString(36)}`;
        break;
      }
      const found = byKey.get(key);
      if (found !== undefined) {
        map[id] = found;
        merged++;
        continue;
      }
      const gid = T + left.length;
      left.push(map[c.left[k]!]!);
      right.push(map[c.right[k]!]!);
      byKey.set(key, gid);
      map[id] = gid;
    }
    for (let k = 0; k < P; k++) outputs[i * P + k] = map[c.outputs[k]!]!;
    if (c.total >= 0) totals[i] = map[c.total]!;
  }
  // prune: keep what partial outputs and totals reach
  const total = T + left.length;
  const used = new Uint8Array(total);
  const stack = [...Array.from(outputs), ...Array.from(totals).filter((x) => x >= 0)];
  while (stack.length) {
    const x = stack.pop()!;
    if (used[x]) continue;
    used[x] = 1;
    if (x >= T) stack.push(left[x - T]!, right[x - T]!);
  }
  const renum = new Int32Array(total).fill(-1);
  for (let x = 0; x < T; x++) renum[x] = x;
  const L2: number[] = [];
  const R2: number[] = [];
  for (let k = 0; k < left.length; k++) {
    if (!used[T + k]) continue;
    renum[T + k] = T + L2.length;
    L2.push(renum[left[k]!]!);
    R2.push(renum[right[k]!]!);
  }
  return {
    h,
    inputs: T,
    left: L2,
    right: R2,
    outputs: outputs.map((x) => renum[x]!),
    totals: totals.map((x) => (x >= 0 ? renum[x]! : -1)),
    mergedAdditions: merged,
    labelling: L,
    localAdditions,
  };
}

export type AlignedBitReport = ReturnType<typeof verifyMerged> & {
  totalsExact: boolean;
  totalsDisjoint: boolean;
  totalsCount: number;
  everyNodeUsedWithTotals: boolean;
  distinctTotals: boolean;
};

/**
 * verifyMerged (supports recomputed through the merged decompositions only; disjointness,
 * common point, exact partial outputs) plus the totals: support of z_i = every triple containing i.
 */
export function verifyAlignedBit(G: AlignedBitGraph): AlignedBitReport {
  const base = verifyMerged(G);
  const { h, inputs: T } = G;
  const triples = tripleList(h);
  const words = (T + 31) >>> 5;
  const memo = new Map<number, Uint32Array>();
  const sup = (x: number): Uint32Array => {
    const m = memo.get(x);
    if (m) return m;
    const s = new Uint32Array(words);
    if (x < T) s[x >>> 5]! |= 1 << (x & 31);
    else {
      const l = sup(G.left[x - T]!);
      const r = sup(G.right[x - T]!);
      for (let w = 0; w < words; w++) s[w] = l[w]! | r[w]!;
    }
    memo.set(x, s);
    return s;
  };
  let exact = G.totals.every((t) => t >= 0);
  let totalsDisjoint = true;
  for (const t of G.totals)
    if (t >= T) {
      // disjointness inside the totals' subtrees (verifyMerged covers only what partial outputs reach)
      const stack = [t];
      const seen = new Set<number>();
      while (stack.length) {
        const x = stack.pop()!;
        if (x < T || seen.has(x)) continue;
        seen.add(x);
        const l = sup(G.left[x - T]!);
        const r = sup(G.right[x - T]!);
        for (let w = 0; w < words; w++) if ((l[w]! & r[w]!) !== 0) totalsDisjoint = false;
        stack.push(G.left[x - T]!, G.right[x - T]!);
      }
    }
  for (let i = 0; i < h && exact; i++) {
    const s = sup(G.totals[i]!);
    for (let t = 0; t < T; t++) if ((((s[t >>> 5]! >>> (t & 31)) & 1) === 1) !== triples[t]!.includes(i)) exact = false;
  }
  // every node used, counting the totals as designated uses
  const used = new Uint8Array(T + G.left.length);
  for (let k = 0; k < G.left.length; k++) used[G.left[k]!] = used[G.right[k]!] = 1;
  for (const o of G.outputs) used[o] = 1;
  for (const t of G.totals) if (t >= 0) used[t] = 1;
  let all = true;
  for (let x = T; x < used.length; x++) if (!used[x]) all = false;
  return { ...base, totalsExact: exact, totalsDisjoint, totalsCount: G.totals.filter((t) => t >= 0).length, everyNodeUsedWithTotals: all, distinctTotals: new Set(G.totals).size === h };
}
