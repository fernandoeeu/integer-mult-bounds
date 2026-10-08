// Independent verification of a merged global graph.
//
// Uses only: h, the list of additions (left/right child ids), and the designated
// outputs given as (node, common point i, target triple T). It does not use the
// labelling, the local circuit, or any key from the builder.
//
// Checks (paired-construction.tex, "Reversible roles and frames in both
// directions", restated in the PR's aligned-paired-review.tex):
//   topo        every addition uses earlier nodes
//   disjoint    every addition joins disjoint supports
//   common      every node's triples share a common point
//   exact       every output equals its defining sum {S : S cap T = {i}},
//               every required coefficient present and every required zero absent
//   oneMeet     every triple of every output meets its target in exactly one point
//   used        every node has an outgoing use (needed for R = c + q)
//   distinct    no two nodes have the same support (interning complete)
//   edgeNest    child support within parent support for every edge (forward
//               frames increase; reversed by complements for the backward graph)
//   roles       role compilation: count equals c + q, every role path nested
//   sim         scalar schedule: J L (z + V x) - J L z = M x (intersection-one map),
//               L^{-1} restores arbitrary scratch, on random dirty data mod p
//   comp3       the three outputs for each target sum to the intersection-one row

import { type GlobalGraph, tripleList, tripleIndex } from "./build";

export type Report = Record<string, number | boolean | string>;

export function verifyGlobal(G: GlobalGraph, opts: { simSeed?: number; firstFail?: (msg: string) => void } = {}): Report {
  const fail = opts.firstFail ?? (() => {});
  const { h, inputs: NT } = G;
  const trips = tripleList(h);
  if (trips.length !== NT) throw new Error("input count");
  const c = G.left.length;
  const total = NT + c;
  const sup: Int32Array[] = new Array(total);
  for (let t = 0; t < NT; t++) sup[t] = Int32Array.of(t);

  let topo = true, disjoint = true, common = true, edgeNest = true;
  let firstNoCommon = -1, firstOverlap = -1;
  let supSum = 0;
  // common point bookkeeping: count per ground point
  const cnt = new Int32Array(h);
  for (let k = 0; k < c; k++) {
    const id = NT + k;
    const l = G.left[k]!, r = G.right[k]!;
    if (!(l < id && r < id)) { topo = false; fail(`topo: node ${id}`); continue; }
    const A = sup[l]!, B = sup[r]!;
    const U = new Int32Array(A.length + B.length);
    let x = 0, y = 0, z = 0, overlap = false;
    while (x < A.length || y < B.length) {
      if (y >= B.length || (x < A.length && A[x]! < B[y]!)) U[z++] = A[x++]!;
      else if (x >= A.length || B[y]! < A[x]!) U[z++] = B[y++]!;
      else { overlap = true; U[z++] = A[x++]!; y++; }
    }
    if (overlap) {
      disjoint = false;
      if (firstOverlap < 0) { firstOverlap = id; fail(`overlap at node ${id}`); }
    }
    const S = z === U.length ? U : U.slice(0, z);
    sup[id] = S;
    supSum += S.length;
    // edge nesting (child within parent): follows from the merge above but checked explicitly
    for (const ch of [A, B]) {
      let p = 0;
      for (const t of ch) {
        while (p < S.length && S[p]! < t) p++;
        if (p >= S.length || S[p] !== t) { edgeNest = false; break; }
      }
    }
    cnt.fill(0);
    for (const t of S) for (const pnt of trips[t]!) cnt[pnt]!++;
    let ok = false;
    for (let pnt = 0; pnt < h; pnt++) if (cnt[pnt] === S.length) ok = true;
    if (!ok) {
      common = false;
      if (firstNoCommon < 0) { firstNoCommon = id; fail(`no common point at node ${id}`); }
    }
  }

  // outputs
  let exact = true, oneMeet = true, firstBadOut = -1;
  const q = G.outNode.length;
  const inT = new Uint8Array(h);
  for (let o = 0; o < q; o++) {
    const i = G.outCommon[o]!;
    const T = trips[G.outTarget[o]!]!;
    if (!T.includes(i)) { exact = false; fail(`output ${o}: common point not in target`); continue; }
    inT.fill(0);
    for (const p of T) inT[p] = 1;
    const S = sup[G.outNode[o]!]!;
    // required support: triples S' with S' cap T = {i}; there are C(h-3, 2) of them,
    // so (sorted, duplicate-free S) exactness = right size + every member qualifies
    const req = ((h - 3) * (h - 4)) / 2;
    for (let j = 1; j < S.length; j++) if (!(S[j - 1]! < S[j]!)) exact = false;
    let good = S.length === req;
    for (const t of S) {
      const tr = trips[t]!;
      const meet = (inT[tr[0]] ? 1 : 0) + (inT[tr[1]] ? 1 : 0) + (inT[tr[2]] ? 1 : 0);
      if (meet !== 1) oneMeet = false;
      if (!(meet === 1 && tr.includes(i))) good = false;
    }
    if (!good) {
      exact = false;
      if (firstBadOut < 0) { firstBadOut = o; fail(`output ${o} (i=${i}, T=${T}) inexact`); }
    }
  }

  // every target T has exactly three outputs, one per point of T
  const perT = new Int32Array(NT);
  const seenIT = new Set<number>();
  let outputsComplete = true;
  for (let o = 0; o < q; o++) {
    perT[G.outTarget[o]!]!++;
    const key = G.outTarget[o]! * h + G.outCommon[o]!;
    if (seenIT.has(key)) outputsComplete = false;
    seenIT.add(key);
  }
  for (let t = 0; t < NT; t++) if (perT[t] !== 3) outputsComplete = false;

  // outgoing uses
  const out = new Int32Array(total);
  for (let k = 0; k < c; k++) { out[G.left[k]!]!++; out[G.right[k]!]!++; }
  for (let o = 0; o < q; o++) out[G.outNode[o]!]!++;
  let used = true, firstUnused = -1;
  for (let x = 0; x < total; x++) if (out[x] === 0) { used = false; if (firstUnused < 0) firstUnused = x; }

  // distinct supports: 53-bit hash, exact comparison on every hash hit
  const seenHash = new Map<number, number[]>();
  let dupSupports = 0;
  const sameArr = (A: Int32Array, B: Int32Array) => A.length === B.length && A.every((v, j) => v === B[j]);
  for (let x = 0; x < total; x++) {
    const S = sup[x]!;
    let h1 = 0x811c9dc5 | 0, h2 = 0x1234567 | 0;
    for (const t of S) { h1 = Math.imul(h1 ^ t, 16777619); h2 = Math.imul(h2 + t, 0x5bd1e995) ^ (h2 >>> 13); }
    const key = (h1 >>> 0) * 2097152 + ((h2 >>> 0) & 0x1fffff) + S.length * 0; // < 2^53
    const bucket = seenHash.get(key);
    if (bucket) {
      if (bucket.some((y) => sameArr(sup[y]!, S))) dupSupports++;
      else bucket.push(x);
    } else seenHash.set(key, [x]);
  }
  seenHash.clear();

  // ---- role compilation and scalar simulation ----
  // Each node's outgoing uses, in order: additions (in node order) then outputs.
  // Inputs: one role per use; the first receives the source copy, the pivot is
  // copied into the others. Addition w = l + r: role(l->w) += role(r->w); the first
  // role becomes w's pivot, copied into fresh roles for w's other uses; role(r->w) retires.
  const useStart = new Int32Array(total + 1);
  for (let x = 0; x < total; x++) useStart[x + 1] = useStart[x]! + out[x]!;
  const useRole = new Int32Array(useStart[total]!).fill(-1);
  const useFill = new Int32Array(total);
  // per-use target id: we only need the role for edge (x -> w); record uses in order
  const roleOfUse = (x: number) => useStart[x]! + useFill[x]!++;
  // gates: kind 0 = copy (dst += src), kind 1 = add (dst += src); both are dst += src
  const gDst: number[] = [], gSrc: number[] = [];
  const roleNode: number[] = []; // node at which each role was created (frame start)
  let roles = 0;
  let rolePathsNested = true;
  // allocate roles for a node: given pivot role (or -1 for input), fill all its uses
  const allocate = (x: number, pivot: number) => {
    const s = useStart[x]!, e = useStart[x + 1]!;
    let first = pivot;
    if (first < 0) { first = roles++; roleNode.push(x); }
    useRole[s] = first;
    for (let u = s + 1; u < e; u++) {
      const r = roles++;
      roleNode.push(x);
      useRole[u] = r;
      gDst.push(r); gSrc.push(first);
    }
  };
  const sourceRole = new Int32Array(NT);
  for (let t = 0; t < NT; t++) { allocate(t, -1); sourceRole[t] = useRole[useStart[t]!]!; }
  // the edges (l -> w), (r -> w) consume the next unused use of l and r, in node order
  const edgeRole = (x: number) => useRole[roleOfUse(x)]!;
  // we must consume uses in the same order they were counted: additions in node order then outputs
  for (let k = 0; k < c; k++) {
    const w = NT + k;
    const a = edgeRole(G.left[k]!);
    const b = edgeRole(G.right[k]!);
    // frame check: both incident roles carry frames of their creating nodes, which must nest in U_w
    for (const r of [a, b]) {
      const z = roleNode[r]!;
      // z is l or r itself, or (for a reused pivot) an ancestor; check sup[z] within sup[w]
      const Z = sup[z]!, W = sup[w]!;
      let p = 0;
      for (const t of Z) { while (p < W.length && W[p]! < t) p++; if (p >= W.length || W[p] !== t) { rolePathsNested = false; break; } }
    }
    gDst.push(a); gSrc.push(b);
    roleNode[a] = w; // the pivot now carries w
    allocate(w, a);
  }
  const outRole = new Int32Array(q);
  for (let o = 0; o < q; o++) outRole[o] = edgeRole(G.outNode[o]!);
  let allUsesConsumed = true;
  for (let x = 0; x < total; x++) if (useFill[x] !== out[x]) allUsesConsumed = false;

  // simulation mod p
  const P = 2147483629; // prime < 2^31
  let seed = (opts.simSeed ?? 12345) >>> 0;
  const rnd = () => { seed = (Math.imul(seed, 1103515245) + 12345) >>> 0; return seed % P; };
  const xs = new Float64Array(NT);
  for (let t = 0; t < NT; t++) xs[t] = rnd();
  const z0 = new Float64Array(roles);
  for (let r = 0; r < roles; r++) z0[r] = rnd();
  const runL = (v: Float64Array) => { for (let g = 0; g < gDst.length; g++) v[gDst[g]!] = (v[gDst[g]!]! + v[gSrc[g]!]!) % P; };
  const runLinv = (v: Float64Array) => { for (let g = gDst.length - 1; g >= 0; g--) v[gDst[g]!] = (v[gDst[g]!]! - v[gSrc[g]!]! + P) % P; };
  const J = (v: Float64Array, y: Float64Array) => { for (let o = 0; o < q; o++) y[G.outTarget[o]!] = (y[G.outTarget[o]!]! + v[outRole[o]!]!) % P; };
  const y = new Float64Array(NT);
  const v = Float64Array.from(z0);
  runL(v); for (let o = 0; o < q; o++) y[G.outTarget[o]!] = (y[G.outTarget[o]!]! - v[outRole[o]!]! + P) % P; runLinv(v);
  let restored1 = true;
  for (let r = 0; r < roles; r++) if (v[r] !== z0[r]) restored1 = false;
  for (let t = 0; t < NT; t++) v[sourceRole[t]!] = (v[sourceRole[t]!]! + xs[t]!) % P; // V
  runL(v); J(v, y); runLinv(v);
  for (let t = 0; t < NT; t++) v[sourceRole[t]!] = (v[sourceRole[t]!]! - xs[t]! + P) % P; // V^{-1}
  let restored2 = true;
  for (let r = 0; r < roles; r++) if (v[r] !== z0[r]) restored2 = false;
  // expected: (M x)_T = sum_{|S cap T| = 1} x_S
  let simExact = true;
  for (let t = 0; t < NT; t++) {
    const T = trips[t]!;
    let s = 0;
    for (const i of T) {
      const rest: number[] = [];
      for (let p = 0; p < h; p++) if (!T.includes(p)) rest.push(p);
      for (let a = 0; a < rest.length; a++)
        for (let b = a + 1; b < rest.length; b++) {
          const k = tripleIndex(h, i, rest[a]!, rest[b]!);
          s = (s + xs[k]!) % P;
        }
    }
    if (s !== y[t]) simExact = false;
  }

  return {
    h,
    additions: c,
    partialOutputs: q,
    rolesCPlusQ: c + q,
    rolesCompiled: roles,
    mergedAdditions: G.mergedAdditions,
    prunedAdditions: G.prunedAdditions,
    starMergeMismatches: G.starMergeMismatches,
    supportSizeSum: supSum,
    topo,
    disjoint,
    common,
    exact,
    oneMeet,
    outputsComplete,
    used,
    firstUnused,
    dupSupports,
    edgeNest,
    rolePathsNested,
    allUsesConsumed,
    simRestoresScratch: restored1 && restored2,
    simExact,
  };
}
