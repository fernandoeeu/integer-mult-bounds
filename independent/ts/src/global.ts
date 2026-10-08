// Cross-group merging, roles, and frame/support checks at ground size h.
//
// Source: paired-construction.tex, end of sec:paired-bit-construction and
// subsection "Reversible roles and frames in both directions".
//
//  - Group i (common point i) is a copy of the local circuit on n = h-1 local
//    vertices; local vertex u stands for ground point g_i(u) = u < i ? u : u+1,
//    and local input x_ab stands for the triple {i, g_i(a), g_i(b)}.
//  - Equal inputs and equal sums are identified across groups. A sum shared by
//    groups i != j consists entirely of triples {i,j,k}; it is identified by the
//    pair {i,j} and the set of k ("fixed pair and variable vertices").
//  - "Keep the first encountered decomposition, in common-point and then
//    local-node order."
//  - Roles: the note compiles 2c + q outgoing uses with c pivot
//    identifications into R = c + q roles. That compilation is NOT checked
//    here: R is computed as c + q, an identity applied to the recomputed c.
//    What is checked is that every node has at least one outgoing use.
//
// The verification half (verifyGlobal) recomputes, for every group i, the
// support of every node reachable from group i's outputs through the merged
// graph, using only the merged decompositions, and checks:
//   * each support is a set of triples that all contain i (common point, hence
//     a nondegenerate positive-definite source span U_z);
//   * every addition joins disjoint supports. A node's span U_z is spanned by
//     the indicators of its support, so along an edge z -> w we get
//     U_z within U_w automatically, and U_w^perp within U_z^perp for the
//     reversed computation; both frame directions therefore reduce to these
//     support facts plus the common-point property;
//   * each designated output of group i for target T = {i,c,d} has support
//     exactly { {i,a,b} : {a,b} disjoint from {c,d} }, so every contributing
//     triple meets T in exactly one point (U_z is contained in t_T^perp).

import { type Circuit, pairIndex } from "./circuit";
import { supportsOf } from "./verifyCircuit";

export type GlobalGraph = {
  h: number;
  inputs: number; // global input ids 0..inputs-1, one per triple
  left: number[];
  right: number[];
  outputs: Int32Array; // outputs[i * P + pairIndex(c,d)], P = C(h-1,2)
  mergedAdditions: number; // local additions identified with an earlier group's node
};

/** Index of the triple {x<y<z} of [h] (lexicographic). */
export function tripleIndex(h: number, pts: number[]): number {
  const [x, y, z] = [...pts].sort((p, q) => p - q) as [number, number, number];
  let idx = 0;
  for (let a = 0; a < x; a++) idx += ((h - a - 1) * (h - a - 2)) / 2;
  for (let b = x + 1; b < y; b++) idx += h - b - 1;
  return idx + (z - y - 1);
}

export function tripleList(h: number): number[][] {
  const out: number[][] = [];
  for (let x = 0; x < h; x++) for (let y = x + 1; y < h; y++) for (let z = y + 1; z < h; z++) out.push([x, y, z]);
  return out;
}

/** For each local node: the local vertex common to every pair of its support (or -1), and the other endpoints. */
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
    // support size >= 2 here; a common vertex is in the first pair and in every other pair
    for (const u of members[0]!) {
      if (members.every(([a, b]) => a === u || b === u)) {
        common[id] = u;
        rest[id] = members.map(([a, b]) => (a === u ? b : a));
      }
    }
  }
  return { pairs, common, rest };
}

export function mergeGroups(local: Circuit, h: number): GlobalGraph {
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
    const g = (u: number) => (u < i ? u : u + 1);
    const map = new Int32Array(P + local.left.length);
    for (let k = 0; k < P; k++) {
      const [a, b] = pairs[k]!;
      map[k] = tripleIndex(h, [i, g(a), g(b)]); // inputs are identified by their triple
    }
    for (let k = 0; k < local.left.length; k++) {
      const id = P + k;
      let key: string;
      if (common[id]! >= 0) {
        const j = g(common[id]!);
        const lo = Math.min(i, j);
        const hi = Math.max(i, j);
        let mask = 0n;
        for (const u of rest[id]!) mask |= 1n << BigInt(g(u));
        key = `P${lo},${hi}:${mask.toString(36)}`;
      } else key = `L${i}:${k}`; // cannot occur in another group (see header)
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
  return { h, inputs: T, left, right, outputs, mergedAdditions: merged };
}

export type GlobalReport = {
  h: number;
  additions: number; // c
  partialOutputs: number; // q
  mergedAdditions: number;
  roles: number; // R = c + q (identity from the note, applied to the recomputed c)
  everyNodeUsed: boolean;
  allAdditionsDisjoint: boolean;
  everyNodeHasCommonPoint: boolean;
  allPartialOutputsExact: boolean;
  outputsOrthogonalToTarget: boolean;
};

export function verifyGlobal(G: GlobalGraph): GlobalReport {
  const { h, inputs: T } = G;
  const n = h - 1;
  const P = (n * (n - 1)) / 2;
  const Wd = (P + 31) >>> 5;
  const total = T + G.left.length;

  // every node (input or addition) must have an outgoing use: a later addition or a designated output
  const used = new Uint8Array(total);
  for (let k = 0; k < G.left.length; k++) used[G.left[k]!] = used[G.right[k]!] = 1;
  for (const o of G.outputs) used[o] = 1;
  let everyNodeUsed = true;
  for (let x = 0; x < total; x++) if (!used[x]) everyNodeUsed = false;

  let allAdditionsDisjoint = true;
  let everyNodeHasCommonPoint = true;
  let exact = true;
  let orthogonal = true;

  for (let i = 0; i < h; i++) {
    const g = (u: number) => (u < i ? u : u + 1);
    const local = new Int32Array(T).fill(-1); // triple -> local pair index in group i
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) local[tripleIndex(h, [i, g(a), g(b)])] = pairIndex(n, a, b);

    const memo = new Map<number, Uint32Array | null>();
    const support = (x: number): Uint32Array | null => {
      const m = memo.get(x);
      if (m !== undefined) return m;
      let s: Uint32Array | null;
      if (x < T) {
        const k = local[x]!;
        if (k < 0) s = null; // a triple without the point i
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
            if ((l[w]! & r[w]!) !== 0) allAdditionsDisjoint = false;
            s[w] = l[w]! | r[w]!;
          }
        }
      }
      if (!s) everyNodeHasCommonPoint = false;
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
        for (let a = 0; a < n; a++)
          for (let b = a + 1; b < n; b++) {
            const k = pairIndex(n, a, b);
            const present = ((s[k >>> 5]! >>> (k & 31)) & 1) === 1;
            const required = a !== c && a !== d && b !== c && b !== d;
            if (present !== required) exact = false;
            if (present) {
              // |{i,g(a),g(b)} intersect {i,g(c),g(d)}| must be 1 for orthogonality to t_T
              const S = [i, g(a), g(b)];
              const Tt = [i, g(c), g(d)];
              if (S.filter((x) => Tt.includes(x)).length !== 1) orthogonal = false;
            }
          }
      }
  }

  return {
    h,
    additions: G.left.length,
    partialOutputs: G.outputs.length,
    mergedAdditions: G.mergedAdditions,
    roles: G.left.length + G.outputs.length,
    everyNodeUsed,
    allAdditionsDisjoint,
    everyNodeHasCommonPoint,
    allPartialOutputsExact: exact,
    outputsOrthogonalToTarget: orthogonal,
  };
}
