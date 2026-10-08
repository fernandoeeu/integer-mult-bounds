// Construction of the merged paired circuit under a chosen per-group labelling.
//
// The local circuit (circuit.ts, copied unchanged from the independent TS
// checker) works on abstract local vertices 0..n-1, n = h-1. Group i (common
// point i) runs it with local vertex u standing for ground point label_i(u),
// so local input x_ab is the triple {i, label_i(a), label_i(b)}.
//
// Labellings:
//   base    : label_i(u) = u < i ? u : u+1          (paired-construction.tex)
//   aligned : label_i = [points except i, i^1 in increasing order] ++ [i^1]
//             (aligned-paired-note.tex, PR 2). Requires h even.
//
// Merge ("intern equal sums"): every local addition of group i is mapped to a
// global node. Two interning keys are supported:
//   support : the exact global support (set of triples). This is the literal
//             meaning of "intern equal sums" and cannot merge unequal sums.
//   star    : the note's key, "fixed pair and variable vertices": a node whose
//             triples all contain two common points {i,j} is keyed by
//             ({i,j}, set of third points); other nodes are never shared.
// The first encountered decomposition (common point order, then local node
// order) is kept. Then unused nodes are pruned (reachability from outputs).

import { type Circuit, pairIndex } from "./circuit";
import { supportsOf } from "./verifyCircuit";

export type Labelling = "base" | "aligned";
export type KeyMode = "support" | "star" | "mutant";
// mutant: negative control only. Star key with the fixed pair dropped, so it merges unequal sums.

export function labelOf(h: number, i: number, kind: Labelling): Int32Array {
  const n = h - 1;
  const lab = new Int32Array(n);
  if (kind === "base") {
    for (let u = 0; u < n; u++) lab[u] = u < i ? u : u + 1;
  } else {
    if (h % 2 !== 0) throw new Error("aligned labelling needs even h");
    const p = i ^ 1;
    let k = 0;
    for (let x = 0; x < h; x++) if (x !== i && x !== p) lab[k++] = x;
    lab[k++] = p;
    if (k !== n) throw new Error("bad labelling");
  }
  return lab;
}

/** Index of the triple {x<y<z} of [h] (lexicographic). */
export function tripleIndex(h: number, a: number, b: number, c: number): number {
  let x = a, y = b, z = c;
  if (x > y) [x, y] = [y, x];
  if (y > z) [y, z] = [z, y];
  if (x > y) [x, y] = [y, x];
  let idx = 0;
  for (let t = 0; t < x; t++) idx += ((h - t - 1) * (h - t - 2)) / 2;
  for (let t = x + 1; t < y; t++) idx += h - t - 1;
  return idx + (z - y - 1);
}

export function tripleList(h: number): [number, number, number][] {
  const out: [number, number, number][] = [];
  for (let x = 0; x < h; x++) for (let y = x + 1; y < h; y++) for (let z = y + 1; z < h; z++) out.push([x, y, z]);
  return out;
}

export type GlobalGraph = {
  h: number;
  inputs: number; // node ids 0..inputs-1: triples in tripleList order
  left: Int32Array;
  right: Int32Array;
  outNode: Int32Array; // designated partial outputs
  outCommon: Int32Array; // common point i of the output
  outTarget: Int32Array; // target triple index T = {i, c, d}
  mergedAdditions: number; // local additions identified with an earlier node
  prunedAdditions: number; // additions removed by pruning after the merge
  starMergeMismatches: number; // star key mode only: merges whose exact supports differ (must be 0)
};

export function mergeGroups(local: Circuit, h: number, kind: Labelling, mode: KeyMode): GlobalGraph {
  const n = h - 1;
  if (local.n !== n) throw new Error("local circuit has the wrong size");
  const P = local.inputs;
  const T = tripleList(h).length;
  const pairs: [number, number][] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) pairs[pairIndex(n, a, b)] = [a, b];

  // local support lists (local pair indices)
  const ls = supportsOf(local);
  const lists: Int32Array[] = ls.map((s) => {
    const xs: number[] = [];
    for (let k = 0; k < P; k++) if ((s[k >>> 5]! >>> (k & 31)) & 1) xs.push(k);
    return Int32Array.from(xs);
  });

  const left: number[] = [];
  const right: number[] = [];
  const byKey = new Map<string, number>();
  const supportOfKey = new Map<string, string>(); // star mode: exact support of the kept node
  let merged = 0;
  let mismatches = 0;
  const outNode: number[] = [];
  const outCommon: number[] = [];
  const outTarget: number[] = [];

  for (let i = 0; i < h; i++) {
    const lab = labelOf(h, i, kind);
    const trip = new Int32Array(P);
    for (let k = 0; k < P; k++) trip[k] = tripleIndex(h, i, lab[pairs[k]![0]]!, lab[pairs[k]![1]]!);
    const exactKey = (id: number) => {
      const t = Array.from(lists[id]!, (k) => trip[k]!).sort((x, y) => x - y);
      let s = "";
      for (let j = 0; j < t.length; j += 4096) s += String.fromCharCode(...t.slice(j, j + 4096));
      return s;
    };
    const map = new Int32Array(P + local.left.length);
    for (let k = 0; k < P; k++) map[k] = trip[k]!;
    for (let k = 0; k < local.left.length; k++) {
      const id = P + k;
      let key: string;
      if (mode === "support") key = exactKey(id);
      else {
        // star key: local vertex common to every local pair of the support
        const mem = lists[id]!;
        let common = -1;
        for (const u of pairs[mem[0]!]!) {
          let all = true;
          for (const m of mem) {
            const [a, b] = pairs[m]!;
            if (a !== u && b !== u) { all = false; break; }
          }
          if (all) common = u;
        }
        if (common >= 0) {
          const j = lab[common]!;
          const third: number[] = [];
          for (const m of mem) {
            const [a, b] = pairs[m]!;
            third.push(lab[a === common ? b : a]!);
          }
          third.sort((x, y) => x - y);
          key = mode === "mutant" ? `M:${third.join(",")}` : `P${Math.min(i, j)},${Math.max(i, j)}:${third.join(",")}`;
        } else key = `L${i}:${k}`;
      }
      const found = byKey.get(key);
      if (found !== undefined) {
        if (mode !== "support" && supportOfKey.get(key) !== exactKey(id)) mismatches++;
        map[id] = found;
        merged++;
        continue;
      }
      const gid = T + left.length;
      left.push(map[local.left[k]!]!);
      right.push(map[local.right[k]!]!);
      byKey.set(key, gid);
      if (mode !== "support") supportOfKey.set(key, exactKey(id));
      map[id] = gid;
    }
    for (let c = 0; c < n; c++)
      for (let d = c + 1; d < n; d++) {
        outNode.push(map[local.outputs[pairIndex(n, c, d)]!]!);
        outCommon.push(i);
        outTarget.push(tripleIndex(h, i, lab[c]!, lab[d]!));
      }
  }

  // prune additions not reachable from any designated output
  const total = T + left.length;
  const used = new Uint8Array(total);
  const stack = [...outNode];
  while (stack.length) {
    const x = stack.pop()!;
    if (used[x]) continue;
    used[x] = 1;
    if (x >= T) stack.push(left[x - T]!, right[x - T]!);
  }
  const renum = new Int32Array(total).fill(-1);
  for (let x = 0; x < T; x++) renum[x] = x;
  const L: number[] = [];
  const R: number[] = [];
  for (let k = 0; k < left.length; k++) {
    if (!used[T + k]) continue;
    renum[T + k] = T + L.length;
    L.push(renum[left[k]!]!);
    R.push(renum[right[k]!]!);
  }
  return {
    h,
    inputs: T,
    left: Int32Array.from(L),
    right: Int32Array.from(R),
    outNode: Int32Array.from(outNode, (x) => renum[x]!),
    outCommon: Int32Array.from(outCommon),
    outTarget: Int32Array.from(outTarget),
    mergedAdditions: merged,
    prunedAdditions: left.length - L.length,
    starMergeMismatches: mismatches,
  };
}
