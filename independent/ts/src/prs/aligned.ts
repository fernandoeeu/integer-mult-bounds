// PR 2 (Andrew Barnes): the aligned relabelling of the paired circuit, rebuilt
// from notes/aligned-paired-note.tex and notes/aligned-paired-review.tex
// ("Construction and local frames"), not from scripts/aligned_paired_network.py.
//
//   "For common point i, order all points except i and i XOR 1 increasingly,
//    then append that partner. Run the unchanged local paired weighted-exclusion
//    circuit in these coordinates. [...] Intern equal fixed-pair star sums using
//    the existing compiler." ... "retain the first decomposition, prune and
//    recompile physical roles."
//
// The merge below is the one of src/global.ts (key: the pair {i, j} and the set of
// third points; first decomposition kept in common-point, then local-node order),
// generalised from the fixed labelling g_i(u) = (u < i ? u : u + 1) to any
// labelling. With the fixed labelling it must reproduce the published
// c = 450394 and 40256 merged additions (a test checks this), which is the
// evidence that the generalisation did not change the merge itself.
//
// After the merge, nodes that no output reaches are pruned ("prune"). Both the
// count before and the count after pruning are reported.

import { type Circuit, pairIndex } from "../circuit";
import { supportsOf } from "../verifyCircuit";
import { tripleIndex, tripleList } from "../global";

/** order[i][u] = ground point that local vertex u stands for in group i. */
export type Labelling = number[][];

/** The labelling of src/global.ts: g_i(u) = u < i ? u : u + 1. */
export function standardLabelling(h: number): Labelling {
  return Array.from({ length: h }, (_, i) => Array.from({ length: h - 1 }, (_, u) => (u < i ? u : u + 1)));
}

/** The aligned labelling of PR 2: increasing points except i and i^1, then i^1. Needs even h. */
export function alignedLabelling(h: number): Labelling {
  if (h % 2 !== 0) throw new Error("the aligned labelling needs even h");
  return Array.from({ length: h }, (_, i) => [...[...Array(h).keys()].filter((j) => j !== i && j !== (i ^ 1)), i ^ 1]);
}

/** Every group's labelling is a bijection from the local vertices onto [h] minus {i}. */
export function labellingIsValid(h: number, L: Labelling): boolean {
  return L.length === h && L.every((o, i) => o.length === h - 1 && new Set(o).size === h - 1 && o.every((x) => x >= 0 && x < h && x !== i));
}

/**
 * Do the local root pairs {2k, 2k+1} (k < 24 at n = 49) map to the same ground pairs in every group?
 * The note: "All complete root pairs now agree across groups."
 * Returns the number of distinct ground pairs that appear as an image of a complete local root pair.
 */
export function rootPairImages(h: number, L: Labelling): { distinct: number; allGlobalPairs: boolean } {
  const n = h - 1;
  const seen = new Set<string>();
  let allGlobal = true;
  for (let i = 0; i < h; i++)
    for (let u = 0; u + 1 < n; u += 2) {
      const a = Math.min(L[i]![u]!, L[i]![u + 1]!);
      const b = Math.max(L[i]![u]!, L[i]![u + 1]!);
      seen.add(`${a},${b}`);
      if (!(a % 2 === 0 && b === a + 1)) allGlobal = false;
    }
  return { distinct: seen.size, allGlobalPairs: allGlobal };
}

function localShape(c: Circuit) {
  const { n, inputs: P } = c;
  const s = supportsOf(c);
  const pairs: [number, number][] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) pairs[pairIndex(n, a, b)] = [a, b];
  const common = new Int32Array(s.length).fill(-1);
  const rest: number[][] = new Array(s.length);
  for (let id = P; id < s.length; id++) {
    const members: [number, number][] = [];
    for (let k = 0; k < P; k++) if ((s[id]![k >>> 5]! >>> (k & 31)) & 1) members.push(pairs[k]!);
    for (const u of members[0]!)
      if (members.every(([a, b]) => a === u || b === u)) {
        common[id] = u;
        rest[id] = members.map(([a, b]) => (a === u ? b : a));
      }
  }
  return { pairs, common, rest };
}

export type MergedGraph = {
  h: number;
  inputs: number;
  left: number[];
  right: number[];
  outputs: Int32Array; // outputs[i * P + pairIndex(c, d)]
  mergedAdditions: number;
  labelling: Labelling;
};

export function mergeWith(local: Circuit, h: number, L: Labelling): MergedGraph {
  const n = h - 1;
  if (local.n !== n) throw new Error("local circuit has the wrong size");
  const P = local.inputs;
  const { pairs, common, rest } = localShape(local);
  const T = tripleList(h).length;
  const left: number[] = [];
  const right: number[] = [];
  const byKey = new Map<string, number>();
  let merged = 0;
  const outputs = new Int32Array(h * P);
  for (let i = 0; i < h; i++) {
    const g = (u: number) => L[i]![u]!;
    const map = new Int32Array(P + local.left.length);
    for (let k = 0; k < P; k++) {
      const [a, b] = pairs[k]!;
      map[k] = tripleIndex(h, [i, g(a), g(b)]);
    }
    for (let k = 0; k < local.left.length; k++) {
      const id = P + k;
      let key: string;
      if (common[id]! >= 0) {
        const j = g(common[id]!);
        let mask = 0n;
        for (const u of rest[id]!) mask |= 1n << BigInt(g(u));
        key = `P${Math.min(i, j)},${Math.max(i, j)}:${mask.toString(36)}`;
      } else key = `L${i}:${k}`;
      const found = byKey.get(key);
      if (found !== undefined) {
        map[id] = found;
        merged++;
        continue;
      }
      const gid = T + left.length;
      left.push(map[local.left[k]!]!);
      right.push(map[local.right[k]!]!);
      byKey.set(key, gid);
      map[id] = gid;
    }
    for (let k = 0; k < P; k++) outputs[i * P + k] = map[local.outputs[k]!]!;
  }
  return { h, inputs: T, left, right, outputs, mergedAdditions: merged, labelling: L };
}

/** Remove additions that no output reaches; renumber in creation order. Returns the pruned graph and the number removed. */
export function pruneMerged(G: MergedGraph): { graph: MergedGraph; removed: number } {
  const T = G.inputs;
  const total = T + G.left.length;
  const used = new Uint8Array(total);
  const stack = Array.from(G.outputs);
  while (stack.length) {
    const x = stack.pop()!;
    if (used[x]) continue;
    used[x] = 1;
    if (x >= T) stack.push(G.left[x - T]!, G.right[x - T]!);
  }
  const renum = new Int32Array(total).fill(-1);
  for (let i = 0; i < T; i++) renum[i] = i;
  const left: number[] = [];
  const right: number[] = [];
  for (let k = 0; k < G.left.length; k++) {
    if (!used[T + k]) continue;
    renum[T + k] = T + left.length;
    left.push(renum[G.left[k]!]!);
    right.push(renum[G.right[k]!]!);
  }
  return { graph: { ...G, left, right, outputs: G.outputs.map((x) => renum[x]!) }, removed: G.left.length - left.length };
}

export type MergedReport = {
  additions: number;
  partialOutputs: number;
  mergedAdditions: number;
  roles: number; // c + q, the note's identity applied to the recomputed c
  everyNodeUsed: boolean;
  allAdditionsDisjoint: boolean;
  everyNodeHasCommonPoint: boolean;
  allPartialOutputsExact: boolean;
  outputsMeetTargetInOnePoint: boolean;
  inputsUsed: number;
};

/**
 * Recompute, for every group i, the support of every node reachable from group i's
 * outputs through the merged decompositions only, and check: disjoint additions,
 * every triple of every node contains i (common point), and every output
 * y_{i,T} = sum_{S cap T = {i}} x_S exactly (review note, "Finite claim F").
 */
export function verifyMerged(G: MergedGraph): MergedReport {
  const { h, inputs: T } = G;
  const n = h - 1;
  const P = (n * (n - 1)) / 2;
  const Wd = (P + 31) >>> 5;
  const total = T + G.left.length;
  const used = new Uint8Array(total);
  for (let k = 0; k < G.left.length; k++) used[G.left[k]!] = used[G.right[k]!] = 1;
  for (const o of G.outputs) used[o] = 1;
  let everyNodeUsed = true;
  let inputsUsed = 0;
  for (let x = 0; x < total; x++) {
    if (!used[x]) everyNodeUsed = false;
    else if (x < T) inputsUsed++;
  }
  let disjoint = true;
  let commonPoint = true;
  let exact = true;
  let onePoint = true;
  for (let i = 0; i < h; i++) {
    const g = (u: number) => G.labelling[i]![u]!;
    const local = new Int32Array(T).fill(-1);
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) local[tripleIndex(h, [i, g(a), g(b)])] = pairIndex(n, a, b);
    const memo = new Map<number, Uint32Array | null>();
    const support = (x: number): Uint32Array | null => {
      const m = memo.get(x);
      if (m !== undefined) return m;
      let s: Uint32Array | null;
      if (x < T) {
        const k = local[x]!;
        if (k < 0) s = null;
        else {
          s = new Uint32Array(Wd);
          s[k >>> 5]! |= 1 << (k & 31);
        }
      } else {
        const l = support(G.left[x - T]!);
        const r = support(G.right[x - T]!);
        if (!l || !r) s = null;
        else {
          s = new Uint32Array(Wd);
          for (let w = 0; w < Wd; w++) {
            if ((l[w]! & r[w]!) !== 0) disjoint = false;
            s[w] = l[w]! | r[w]!;
          }
        }
      }
      if (!s) commonPoint = false;
      memo.set(x, s);
      return s;
    };
    for (let c = 0; c < n; c++)
      for (let d = c + 1; d < n; d++) {
        const s = support(G.outputs[i * P + pairIndex(n, c, d)]!);
        if (!s) {
          exact = false;
          continue;
        }
        const Tt = [i, g(c), g(d)];
        for (let a = 0; a < n; a++)
          for (let b = a + 1; b < n; b++) {
            const k = pairIndex(n, a, b);
            const present = ((s[k >>> 5]! >>> (k & 31)) & 1) === 1;
            const required = a !== c && a !== d && b !== c && b !== d;
            if (present !== required) exact = false;
            if (present && [i, g(a), g(b)].filter((x) => Tt.includes(x)).length !== 1) onePoint = false;
          }
      }
  }
  return {
    additions: G.left.length,
    partialOutputs: G.outputs.length,
    mergedAdditions: G.mergedAdditions,
    roles: G.left.length + G.outputs.length,
    everyNodeUsed,
    allAdditionsDisjoint: disjoint,
    everyNodeHasCommonPoint: commonPoint,
    allPartialOutputsExact: exact,
    outputsMeetTargetInOnePoint: onePoint,
    inputsUsed,
  };
}
