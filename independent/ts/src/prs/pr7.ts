// PR 7 (jacklightChen): "Add ternary five-subset witness for conditional
// 373/10^11 > 2^-28". Head 6725c6a, base 6e56487. Commit c15ca16 imports PR 3 and
// PR 5 byte-identically; commit 6725c6a adds notes/prime-field28-note.tex,
// notes/prime-field28-construction.tex, docs/research/prime-field28.md,
// certificates/prime-field28.json, patches/prime-field28.patch and the scripts.
//
// Top-down: both finite networks change; the assembly is PR 5's.
//  (1) Bit (interchange) network: a new motif over F3 on the five-subsets of h = 28
//      points, v = C(28,5) = 98280, m = h^3 = 21952, label form H = I - (2/25)J.
//      For every common pair C a local triple-exclusion producer on the other 26
//      points; outputs D_{C,E} (q = 10v) and retained totals A_C (C(h,2) = 378).
//      After global identification 11240978 additions; resynthesizing the 20475
//      four-point stars (365 templates) replaces 3006276 additions by 2623060, so
//      c = 10857762, q = 983178, R = 11840940. Retained outputs lose h - 2 each:
//      L_b = 3v^2 C(h,2)(h-2). Banks shared: W_b = 2v^2(v + R), s_b = W_b m - N + 2L_b,
//      eta_b = 39/520019360 > (3/4*10^-8)(9997/1000), log 21952 < 9997/1000, so
//      a = 3/400000000 (tau = 1 - a).
//  (2) Complex network: PR 3's motif at h = 28 with the same triple-exclusion
//      producer at n = 28 as its disjoint producer: 61022 additions, 32816 pieces,
//      R_c = 93838; banks shared: W_c = 2v^2(v + R_c + h + 1), L_c = 3v^2 h(h+1),
//      s_c = W_c m - 2v^3 + 2L_c, eta_c = 5/12693352 > (39/10^9) 10, log m_c < 10.
//  (3) PR 5's fast-Gaussian assembly with eps = 4999/10000, c = 9999/10000,
//      beta = 19/25, lambda = 1 - 749/10^11, lambda' = 1 - 748/10^11,
//      kappa = 373/10^11; G_* = g3 = 934813/(25*10^13), gap 2313/(25*10^13).
//
// What the arithmetic depends on most: the bit role count. a = 3/4*10^-8 needs
// R <= 11844074 (3134 spare); without the star resynthesis R = 12224156 and a
// fails. So the star count is rebuilt here at the stated size.

import { q, add, sub, mul, div, lt, le, eq, twoPow, ONE, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { layerExponents, compactParameterChecks, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { compressedNetwork } from "./pr3";
import { fastParameterChecks, fastMargins, fastMinimumMargin, guardBetaThreshold, leafAndGuardCompatible, exactPowerInstance, cutoff64d2, cutoff96d, DROPPED } from "./fastGaussian";
import { buildPairedTriple } from "./pairedTriple";
import { buildComplexCircuit, verifyComplexCircuit } from "./complexCircuit";
import { mergeProducers, prune, starDemands, resynthesize, fingerprintCount } from "./primeField";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const NOTE = "PR7 prime-field28-note.tex";
const CON = "PR7 prime-field28-construction.tex";
const DOC = "PR7 prime-field28.md";
const PATCH = "PR7 prime-field28.patch 08-assembly";
const H = 28;

export const STATED_PR7 = {
  // local producer ("Cancellation-free triple exclusion")
  localAdditions: 41427,
  retainedAncestors: 12,
  localOutputs: 2600,
  // global producer
  globalAdditions: 11240978,
  q: 983178n,
  stars: 20475,
  templates: 365,
  oldStar: 3006276,
  newStar: 2623060,
  c: 10857762n,
  R: 11840940n,
  // bit network
  v: 98280n,
  m: 21952n,
  exceptional: q(-31n, 25n),
  W: 230640858616896000n,
  s: 5063027748645128371200n,
  eta: q(39n, 520019360n),
  a: q(3n, 400000000n),
  L0: q(9997n, 1000n),
  matchingImages: 98280, // docs: "All 98,280 matching images are distinct"
  // complex network
  cAdditions: 61022,
  cPieces: 32816,
  Rc: 93838n,
  vc: 3276n,
  Wc: 2085111546336n,
  etac: q(5n, 12693352n),
  ac: q(39n, TEN(9)),
  L0c: q(10n),
  // assembly
  C1: q(19601n, 10000n),
  G: q(934813n, 250000000000000n),
  gap: q(2313n, 250000000000000n),
  alphaExp: q(5001n, 20000n),
  KExp: q(49985001n, TEN(8)),
  ellExp: q(5001n, 10000n),
  primeExp: q(1n, 5000n),
};

export function pr7Params(): CompactParams {
  const a = q(3n, 400000000n);
  const ac = q(39n, TEN(9));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(4999n, 10000n),
    c: q(9999n, 10000n),
    beta: q(19n, 25n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(19601n, 10000n),
    lambda: sub(ONE, q(749n, TEN(11))),
    lambdaPrime: sub(ONE, q(748n, TEN(11))),
    kappa: q(373n, TEN(11)),
  };
}

/** The F3 bit network's counts from the interface formulas (construction note). */
export function primeFieldBitNetwork(h: number, R: bigint) {
  const H_ = BigInt(h);
  const v = binom(H_, 5n);
  const m = H_ ** 3n;
  const N = v ** 3n;
  const L = 3n * v * v * binom(H_, 2n) * (H_ - 2n);
  const W = 2n * v * v * (v + R);
  const s = W * m - N + 2n * L;
  return { v, m, N, L, W, s, D: W * m - s, eta: q(W * m - s, W * m) };
}

/** PR 7's complex network: PR 3's interface with stage-1/stage-3 banks shared (2v^2 instead of 3v^2). */
export function primeFieldComplexNetwork(h: number, R: bigint) {
  const H_ = BigInt(h);
  const v = binom(H_, 3n);
  const m = H_ ** 3n;
  const N = v ** 3n;
  const W = 2n * v * v * (v + R + H_ + 1n);
  const L = 3n * v * v * H_ * (H_ + 1n);
  const s = W * m - 2n * N + 2n * L;
  return { v, m, N, I: 3n * v * v, W, L, s, D: W * m - s, eta: q(W * m - s, W * m) };
}

/** Largest R with (deficit numerator)/(denominator(R)) > a L0, for eta = num/(k (base + R)). */
export function largestR(num: bigint, k: bigint, base: bigint, a: Q, L0: Q) {
  // eta(R) = num / (k (base + R)) > a L0  <=>  base + R < num / (k a L0)
  // (bit: eta_b = (N - 2L_b)/(W_b m) = (v - 6 C(h,2)(h-2)) / (2m (v + R)))
  const bound = div(q(num), mul(q(k), mul(a, L0)));
  const fl = bound.num / bound.den;
  const strictMax = bound.den === 1n ? fl - 1n : fl; // largest integer < bound
  return strictMax - base;
}

/**
 * The explicit five-set matching pi of "Sharing first- and third-stage banks": pair the points
 * {2k, 2k+1}. No full pair: keep the singletons in the two least indexed pairs, flip the other
 * three. One full pair: keep it, flip the three singletons. Two full pairs {p,q} and a singleton
 * in pair r: flip the singleton and move {p,q} to the next edge of an Euler circuit of the
 * complete graph on the other pair indices (constructed here; the note fixes none).
 */
export function fiveSetMatching(h: number) {
  const P = h / 2;
  if (h % 4 !== 0) throw new Error("the complete graph on the other h/2 - 1 pair indices has an Euler circuit only when h/2 - 2 is even");
  // Euler circuit of K_{P-1} on the pair indices other than r, by Hierholzer; successor map on edges
  const succ = new Map<number, Map<string, [number, number]>>();
  for (let r = 0; r < P; r++) {
    const verts = [...Array(P).keys()].filter((x) => x !== r);
    const adj = new Map<number, Set<number>>();
    for (const x of verts) adj.set(x, new Set(verts.filter((y) => y !== x)));
    const stack = [verts[0]!];
    const circuit: number[] = [];
    while (stack.length) {
      const x = stack[stack.length - 1]!;
      const nb = adj.get(x)!;
      if (nb.size) {
        const y = Math.min(...nb);
        nb.delete(y);
        adj.get(y)!.delete(x);
        stack.push(y);
      } else circuit.push(stack.pop()!);
    }
    const edges: [number, number][] = [];
    for (let i = 0; i + 1 < circuit.length; i++) edges.push([circuit[i]!, circuit[i + 1]!]);
    const m = new Map<string, [number, number]>();
    edges.forEach(([a, b], i) => {
      const [c, d] = edges[(i + 1) % edges.length]!;
      m.set(`${Math.min(a, b)},${Math.max(a, b)}`, [Math.min(c, d), Math.max(c, d)]);
    });
    succ.set(r, m);
  }
  const pi = (T: number): number => {
    const pairs: number[] = [];
    const full: number[] = [];
    const single: number[] = [];
    for (let k = 0; k < P; k++) {
      const b = (T >>> (2 * k)) & 3;
      if (b === 3) full.push(k);
      else if (b) single.push(2 * k + (b === 2 ? 1 : 0));
      if (b) pairs.push(k);
    }
    let out = 0;
    if (full.length === 0) {
      single.forEach((x, i) => (out |= 1 << (i < 2 ? x : x ^ 1)));
    } else if (full.length === 1) {
      out |= 3 << (2 * full[0]!);
      for (const x of single) out |= 1 << (x ^ 1);
    } else {
      const s = single[0]!;
      const [p, q2] = succ.get(s >> 1)!.get(`${full[0]},${full[1]}`)!;
      out = (1 << (s ^ 1)) | (3 << (2 * p)) | (3 << (2 * q2));
    }
    return out;
  };
  const pop = (x: number) => {
    let c = 0;
    while (x) {
      x &= x - 1;
      c++;
    }
    return c;
  };
  const seen = new Set<number>();
  let domain = 0;
  let allTwo = true;
  let classesPreserved = true;
  const fullPairs = (T: number) => {
    let c = 0;
    for (let k = 0; k < P; k++) if (((T >>> (2 * k)) & 3) === 3) c++;
    return c;
  };
  for (let T = 0; T < 1 << h; T++) {
    if (pop(T) !== 5) continue;
    domain++;
    const U = pi(T);
    if (pop(U) !== 5) allTwo = false;
    seen.add(U);
    if (pop(T & U) !== 2) allTwo = false;
    if (fullPairs(T) !== fullPairs(U)) classesPreserved = false;
  }
  return { domain, distinct: seen.size, allTwo, classesPreserved };
}

/** The rank over Q of the source indicators of a retained total A_C (lower bound mod a prime; upper bound by two linear relations). */
export function retainedSpanRank(h: number) {
  const p = 1000003;
  const C = [0, 1];
  const rows: number[][] = [];
  const rest = [...Array(h).keys()].filter((x) => !C.includes(x));
  for (let i = 0; i < rest.length; i++)
    for (let j = i + 1; j < rest.length; j++)
      for (let k = j + 1; k < rest.length; k++) {
        const r = new Array(h).fill(0);
        for (const x of [...C, rest[i]!, rest[j]!, rest[k]!]) r[x] = 1;
        rows.push(r);
      }
  // Gaussian elimination mod p
  let rank = 0;
  const M = rows.map((r) => [...r]);
  for (let col = 0; col < h && rank < M.length; col++) {
    let piv = -1;
    for (let r = rank; r < M.length; r++) if (M[r]![col]! % p !== 0) { piv = r; break; }
    if (piv < 0) continue;
    [M[rank], M[piv]] = [M[piv]!, M[rank]!];
    const inv = modInv(M[rank]![col]!, p);
    for (let r = 0; r < M.length; r++) {
      if (r === rank || M[r]![col]! === 0) continue;
      const f = (M[r]![col]! * inv) % p;
      for (let c = col; c < h; c++) M[r]![c] = (((M[r]![c]! - f * M[rank]![c]!) % p) + p) % p;
    }
    rank++;
  }
  // every row satisfies u_0 = u_1 and 3 u_0 = sum of the other coordinates: rank <= h - 2 over Q
  const relations = rows.every((r) => r[0] === r[1] && 3 * r[0]! === r.slice(2).reduce((s, x) => s + x, 0));
  return { rankModP: rank, relations, rows: rows.length };
}
function modInv(a: number, p: number) {
  let [r0, r1, s0, s1] = [a % p, p, 1, 0];
  while (r1) {
    const qq = Math.floor(r0 / r1);
    [r0, r1] = [r1, r0 - qq * r1];
    [s0, s1] = [s1, s0 - qq * s1];
  }
  return ((s0 % p) + p) % p;
}

export function computeLocal7() {
  return cached("pr7 local", () => buildPairedTriple(H - 2, true));
}
export function computeComplex7() {
  return cached("pr7 complex", () => verifyComplexCircuit(buildComplexCircuit(H, "leftFold", false, buildPairedTriple(H, false).graph)));
}
/** The heavy global build (about 1 minute, 1.8 GB at h = 28). Only the summary is kept. */
export function computeGlobal7(h = H) {
  return cached(`pr7 global ${h}`, () => {
    if (typeof Bun !== "undefined") Bun.gc(true); // the build needs about 1.8 GB at h = 28; start from a collected heap
    const local = h === H ? computeLocal7() : buildPairedTriple(h - 2, true);
    const G = mergeProducers(h, local.graph);
    const pr = prune(G);
    const d = starDemands(G, pr.active);
    const rs = resynthesize(G, d);
    const summary = {
      h,
      v: G.v,
      unique: G.uniqueAdditions,
      byCoreSize: G.byCoreSize,
      merged: G.merged,
      contexts: G.contexts,
      roots: G.roots.length,
      active: pr.additions,
      removed: pr.removed,
      inputsActive: pr.inputs,
      topological: pr.topological,
      stars: d.stars,
      starsRequested: d.demand.size,
      oldStar: d.oldStarAdditions,
      templates: rs.templates,
      newStar: rs.newStarAdditions,
      templatesValid: rs.allTemplatesValid,
      unrequestedStars: rs.unrequestedStars,
      c: pr.additions - d.oldStarAdditions + rs.newStarAdditions,
      // the canonical request lists with their star counts (kept for PR 9's re-synthesis; small)
      templateList: [...rs.cache.values()].map((t) => ({ targets: t.targets, uses: t.uses, published: t.gates.length })),
    };
    return summary; // the graph itself is not kept
  });
}

export type PR7Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR7>; observation?: boolean; global?: ReturnType<typeof computeGlobal7> };

export function pr7(opts: PR7Options = {}) {
  const st = { ...STATED_PR7, ...opts.stated };
  const p = opts.p ?? pr7Params();
  const out: Result[] = [];
  const OBS = "PR7-0 observations (not part of the claim)";

  // ---- 7A: the local producer
  const SA = "PR7-A local triple-exclusion producer, n = 26 (rebuilt; construction order from the PR's script, see caveats)";
  const loc = computeLocal7().report;
  out.push(
    equals(SA, "active additions (reachable from the 2600 outputs)", CON + ": its 41427 active additions", loc.additions, st.localAdditions),
    equals(SA, "retaining the total adds twelve ancestors", CON, loc.retainedAdditions - loc.additions, st.retainedAncestors),
    equals(SA, "outputs = C(26,3)", CON + ": all C(26,3) = 2600 output coefficient vectors", loc.outputs, st.localOutputs),
    truth(SA, "every output = sum of the triples disjoint from its triple (supports recomputed from the kept additions)", CON, loc.outputsExact),
    truth(SA, "the retained total = sum of all 2600 inputs", CON, loc.totalExact),
    truth(SA, "every addition joins disjoint supports", CON, loc.allDisjoint),
    equals(SA, "nonzero output coefficients = 2600 C(23,3)", CON, BigInt(loc.nonzeroCoefficients), 2600n * binom(23, 3), "identity"),
    truth(SA, "additions by number of common points of the support", "certificate field (compared in compare:prs)", true, JSON.stringify(loc.byCore), "observation"),
  );

  // ---- 7B: the global producer and the star resynthesis
  const SB = "PR7-B global producer at h = 28: identification over the C(28,2) common pairs, four-point star resynthesis (rebuilt at the stated size)";
  const G = opts.global ?? computeGlobal7();
  const v = binom(BigInt(H), 5n);
  const qq = BigInt(G.roots);
  out.push(
    equals(SB, "contexts = C(h,2)", CON, G.contexts, Number(binom(H, 2)), "identity"),
    equals(SB, "addition nodes after identifying equal supports", CON + ": There are 11240978 addition nodes", G.unique, st.globalAdditions),
    equals(SB, "unused ancestors removed after identification", "certificate removed_after_merging (the note: then remove unused ancestors)", G.removed, 0, "observation"),
    truth(SB, "every five-set input is used, and every addition's children precede it", CON, G.inputsActive === Number(v) && G.topological),
    equals(SB, "designated output uses q (2600 per pair plus the retained total)", CON + ": q = 10v + C(h,2) = 983178", qq, st.q),
    equals(SB, "q = 10 v + C(h,2)", CON, 10n * v + binom(H, 2), st.q, "identity"),
    equals(SB, "stars with at least one addition = C(28,4)", CON + ": The 20475 stars", G.stars, st.stars),
    equals(SB, "star additions before replacement", CON + ": replaces 3006276 additions", G.oldStar, st.oldStar),
    equals(SB, "distinct relabelled request lists (templates)", CON + ": require 365 distinct templates", G.templates, st.templates),
    equals(SB, "additions of the greedy replacement circuits", CON + ": by at most 2623060", G.newStar, st.newStar),
    truth(SB, "every template gate joins two available disjoint terms, makes a new sum, and every requested sum is made", CON, G.templatesValid),
    equals(SB, "every star has a request (no star is dropped)", CON, G.unrequestedStars, 0, "implied"),
    equals(SB, "c = 11240978 - 3006276 + 2623060", CON + ": c = 10857762", BigInt(G.c), st.c),
    equals(SB, "R = c + q", CON + ": R = c + q = 11840940", BigInt(G.c) + qq, st.R),
    truth(SB, "unique additions by |common points| (2 = one context, 3 and 4 shared keys) and local additions identified with existing nodes", CON, true, `${JSON.stringify(G.byCoreSize)}; identified ${G.merged}`, "observation"),
  );

  // ---- 7C: the F3 bit network
  const SC = "PR7-C F3 five-subset interchange network: counts, eta_b, a = 3/(4*10^8)";
  const R = BigInt(G.c) + qq;
  const bn = primeFieldBitNetwork(H, R);
  const logm = cached("pr7 logm", () => logIntegerEnclosure(bn.m, 24));
  const expL0 = cached("pr7 exp", () => expLowerBound(st.L0, 80));
  const enc = savingEnclosure(bn.eta, logm);
  const mt = cached("pr7 matching", () => fiveSetMatching(H));
  const span = cached("pr7 span", () => retainedSpanRank(H));
  const Rmax = largestR(v - 6n * binom(H, 2) * BigInt(H - 2), 2n * bn.m, v, st.a, st.L0);
  out.push(
    equals(SC, "v = C(28,5)", CON, bn.v, st.v),
    equals(SC, "m = h^3", CON, bn.m, st.m),
    equals(SC, "exceptional eigenvalue of H = I - (2/25)J is 1 - 2h/25", CON, sub(ONE, q(2n * BigInt(H), 25n)), st.exceptional, "identity"),
    truth(SC, "<t_S, t_T>_H = |S cap T| - 2 and <t_T, t_T>_H = 3 for five-sets (2*5*5/25 = 2)", CON, eq(q(2n * 25n, 25n), q(2n)), "", "identity"),
    truth(SC, "scatter minus injection: C(k,2) - [k=2] = [k=5] mod 3 for k = 0..5", CON, [0, 1, 2, 3, 4, 5].every((k) => (((k * (k - 1)) / 2 - (k === 2 ? 1 : 0)) % 3 + 3) % 3 === (k === 5 ? 1 : 0)), "", "constant"),
    truth(SC, "the source span of a retained total A_C has dimension h - 2 = 26 (rank mod 1000003 >= 26; two linear relations give <= 26)", CON + ": its source span has dimension h-2", span.rankModP === H - 2 && span.relations, `rank ${span.rankModP} on ${span.rows} indicators`),
    equals(SC, "W_b = 2 v^2 (v + R)", CON, bn.W, st.W),
    equals(SC, "s_b = W_b m - N + 2 L_b", CON, bn.s, st.s),
    truth(SC, "2 L_b < N (positive deficit)", CON, 2n * bn.L < bn.N),
    equals(SC, "eta_b = (W_b m - s_b)/(W_b m)", CON, bn.eta, st.eta),
    fromCheck(SC, { name: "log 21952 < 9997/1000 (atanh, 24 terms)", source: CON, lhs: logm.upper, rel: "<", rhs: st.L0 }),
    truth(SC, "e^(9997/1000) > 21952 (Taylor partial sum, second route)", CON, lt(q(bn.m), expL0)),
    fromCheck(SC, { name: "eta_b > a (9997/1000), a = 3/(4*10^8)", source: CON, lhs: mul(st.a, st.L0), rel: "<", rhs: bn.eta }),
    truth(SC, "a < lower enclosure of the actual saving -log(1 - eta_b)/log m (Mercator route)", CON, lt(st.a, enc.lower), `a* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    truth(SC, "a = 3/400000000 = 7.5e-9", DOC, toDecimal(st.a, 10) === "0.0000000075", toDecimal(st.a, 12)),
    fromCheck(SC, { name: "1 - tau <= a", source: NOTE, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    equals(SC, "matching pi: images of all C(28,5) five-sets are distinct", DOC + ": All 98,280 matching images are distinct", mt.distinct, st.matchingImages),
    truth(SC, "matching pi: |T cap pi(T)| = 2 for every five-set, and the three classes are preserved (Euler circuit constructed here)", CON, mt.allTwo && mt.classesPreserved && mt.domain === Number(v)),
    truth(OBS, "role budget: the largest R certifying a = 3/(4*10^8) with log m < 9997/1000", "derived", true, `R <= ${Rmax}; stated R = ${R} leaves ${Rmax - R} roles (${toDecimal(q(Rmax - R, R), 6)} of R)`, "observation"),
    truth(OBS, "without the star resynthesis (R = 11240978 + 983178) a = 3/(4*10^8) would not be certified", "derived", !lt(mul(st.a, st.L0), primeFieldBitNetwork(H, BigInt(G.unique) + qq).eta), `R = ${BigInt(G.unique) + qq} > ${Rmax}`, "observation"),
  );

  // ---- 7D: the complex network at h = 28
  const SD = "PR7-D complex network at h = 28 with the triple-exclusion producer (PR 3's motif; circuit rebuilt)";
  const cc = computeComplex7();
  const Rc = BigInt(cc.additions + cc.injections);
  const cn = primeFieldComplexNetwork(H, Rc);
  const logmc = cached("pr7 logmc", () => logIntegerEnclosure(cn.m, 24));
  const encc = savingEnclosure(cn.eta, logmc);
  const gates = 3n * cn.v * cn.v * (4n * (BigInt(cc.additions) + cn.v) + 4n * cn.v + 4n);
  const pr3form = compressedNetwork(H, Rc); // PR 3's formula without bank sharing, for the observation
  // eta_c = (2N - 2L_c)/(W_c m) = (v - 3h(h+1)) / (m (v + h + 1 + R_c))
  const RcMax = largestR(cn.v - 3n * BigInt(H) * BigInt(H + 1), cn.m, cn.v + BigInt(H) + 1n, st.ac, st.L0c);
  out.push(
    equals(SD, "additions", CON + ": 61022 additions", cc.additions, st.cAdditions),
    equals(SD, "injected pieces (after the PR 3 splitting rule)", CON + ": 32816 injected pieces", cc.injections, st.cPieces),
    equals(SD, "R_c = additions + pieces", CON + ": R_c = 93838", Rc, st.Rc),
    truth(SD, "side map exact: +1/2 on every disjoint triple, -1/2 on every intersection-two triple, each once", CON, cc.sideMapExact),
    truth(SD, "every addition joins disjoint supports", CON, cc.allAdditionsDisjoint),
    equals(SD, "nonzero side coefficients = v (C(25,3) + 3*25)", CON, BigInt(cc.nonzeroCoefficients), cn.v * (binom(25, 3) + 75n), "identity"),
    equals(SD, "pair-star additions = 2(h-5) C(h,2) (PR 3's chains, unchanged)", CON, cc.starAdditions, 2 * (H - 5) * Number(binom(H, 2)), "identity"),
    truth(SD, "disjoint / pair-star additions, split pieces", "certificate fields (compared in compare:prs)", true, `${cc.disjointAdditions} / ${cc.starAdditions}; split ${cc.splitDisjoint} disjoint and ${cc.splitStar} pair-star pieces; ${cc.piecesPerTarget.min}..${cc.piecesPerTarget.max} pieces per target`, "observation"),
    equals(SD, "v_c = C(28,3)", CON, cn.v, st.vc),
    equals(SD, "W_c = 2 v^2 (v + R_c + h + 1)", CON, cn.W, st.Wc),
    equals(SD, "eta_c = (W_c m - s_c)/(W_c m), s_c = W_c m - 2v^3 + 2 L_c, L_c = 3v^2 h(h+1)", CON, cn.eta, st.etac),
    truth(SD, "L_c < N (positive deficit)", CON, cn.L < cn.N),
    fromCheck(SD, { name: "log 21952 < 10", source: CON, lhs: logmc.upper, rel: "<", rhs: st.L0c }),
    fromCheck(SD, { name: "eta_c > (39/10^9) 10", source: CON, lhs: mul(st.ac, st.L0c), rel: "<", rhs: cn.eta }),
    truth(SD, "a_c < lower enclosure of the actual complex saving (Mercator route)", CON, lt(st.ac, encc.lower), `a_c* in [${toDecimal(encc.lower, 14)}, ${toDecimal(encc.upper, 14)}]`),
    fromCheck(SD, { name: "scalar gates 3v^2(4(61022 + 3276) + 4v + 4) < 12 W_c", source: CON, lhs: q(gates), rel: "<", rhs: q(12n * cn.W) }),
    truth(SD, "the triple map flipping every point to its partner is an involution with |T cap T'| even", CON, (() => {
      for (let a = 0; a < H; a++) for (let b = a + 1; b < H; b++) for (let c = b + 1; c < H; c++) {
        const T = [a, b, c];
        const U = T.map((x) => x ^ 1);
        const k = T.filter((x) => U.includes(x)).length;
        if (k % 2) return false;
      }
      return true;
    })(), "", "constant"),
    fromCheck(SD, { name: "1 - sigma <= a_c", source: NOTE, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    truth(OBS, "complex role budget for a_c = 39/10^9 with log m_c < 10", "derived", true, `R_c <= ${RcMax}; stated ${Rc} leaves ${RcMax - Rc}`, "observation"),
    truth(OBS, "without bank sharing (PR 3's 3v^2 form) this circuit would give", "derived", true, `eta_c = ${show(pr3form.eta)} (${toDecimal(pr3form.eta, 12)}), below a_c * 10 = ${toDecimal(mul(st.ac, st.L0c), 12)}: ${lt(pr3form.eta, mul(st.ac, st.L0c)) ? "the sharing is needed" : "not needed"}`, "observation"),
  );

  // ---- 7E: assembly (PR 5's fast-Gaussian system) and guard
  const SE = "PR7-E assembly: PR 5's fast-Gaussian parameter system with the new savings";
  const x = layerExponents(p);
  const mg = fastMargins(p);
  const Gm = fastMinimumMargin(p);
  const thr = guardBetaThreshold(p);
  out.push(...fastParameterChecks(p).map((k) => fromCheck(SE, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SE, { name: `kappa < ${k}`, source: PATCH + " eq:margin-list (g5 = 1 - delta - 2 eps)", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SE, "sigma < tau, so chi = tau", NOTE, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SE, "C1 = 5 - 4 beta + zeta = 19601/10000", CON, sub(add(q(5n), p.zeta), mul(q(4n), p.beta)), st.C1),
    fromCheck(SE, { name: "beta > (5 + zeta - 1/eps)/4 (the guard threshold; same as eps C1 < 1)", source: "PR5 fast-gaussian-note.tex", lhs: thr, rel: "<", rhs: p.beta, kind: "implied" }),
    truth(SE, "with PR 3's a_c = 14/10^9 no beta would meet both the guard and the leaf at this eps and kappa", "derived (cf. PR 5's statement for 418/10^12)", !leafAndGuardCompatible(p, q(14n, TEN(9))), `needs a_c > ${toDecimal(div(div(p.kappa, p.epsilon), sub(ONE, thr)), 14)}`, "observation"),
    truth(SE, "with a_c = 39/10^9 such a beta exists", NOTE, leafAndGuardCompatible(p, p.ac)),
    equals(SE, "G_* = g3", CON, Gm, mg.g3),
    equals(SE, "G_* = g3 = 934813/(25*10^13)", CON, Gm, st.G),
    equals(SE, "G_* - kappa = 2313/(25*10^13)", CON, sub(Gm, p.kappa), st.gap),
    equals(SE, "alpha exponent (1 - eps)/2 = 5001/20000", PATCH, div(sub(ONE, p.epsilon), q(2n)), st.alphaExp),
    equals(SE, "K exponent eps c = 49985001/10^8", PATCH, mul(p.epsilon, p.c), st.KExp),
    equals(SE, "ell exponent 1 - eps = 5001/10000", PATCH, sub(ONE, p.epsilon), st.ellExp),
    equals(SE, "prime-interval ratio and b/d^2 grow as p^(1 - 2 eps) = p^(1/5000)", PATCH, sub(ONE, mul(q(2n), p.epsilon)), st.primeExp),
    fromCheck(SE, { name: "kappa > 2^-28", source: NOTE, lhs: twoPow(-28), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SE, { name: "kappa < 2^-27", source: "derived (the dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-27), kind: "condition" }),
  );
  const old = compactParameterChecks(p).filter((k) => DROPPED.includes(k.name));
  for (const k of old)
    out.push(truth(OBS, `PR 3's condition "${k.name}" at eps = 4999/10000 (dropped by PR 5's patch)`, "PR3 complex-circuit-31.patch", true, `${(k.rel === "<" ? lt(k.lhs, k.rhs) : le(k.lhs, k.rhs)) ? "holds" : "fails"} (lhs ${toDecimal(k.lhs, 6)}, rhs ${toDecimal(k.rhs, 6)})`, "observation"));

  const SG = "PR7-F generalized guard with the new complex network (m_c = 21952, beta = 19/25)";
  const gu = compactGuardConstants(cn.W, cn.s, cn.m, p.zeta);
  out.push(...compactGuardChecks(cn.W, cn.s, cn.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SG, k)));
  const depth = cached(`pr7 depth ${show(p.beta)} ${cn.s}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], cn.m, cn.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SG, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));

  // ---- 7G: Gaussian width at the new eps (PR 5's lemma; instances only)
  const SW = "PR7-G Gaussian width alpha = floor(sqrt(b/(8d))) at eps = 4999/10000 (PR 5's construction)";
  for (const k of [30000, 40000, 50000]) {
    const r = cached(`pr7 inst ${k} ${show(p.epsilon)}`, () => {
      try {
        return exactPowerInstance(k, p.epsilon);
      } catch {
        return null;
      }
    });
    const ok = !!r && Object.values(r.facts).every(Boolean);
    out.push(truth(SW, `b = 2^${k}, d = floor(b^eps) exact: every stated bound (b >= 96d, b >= 64d^2, alpha >= 2, alpha^2 >= b/(16d), alpha^2 < p, gamma <= b/4, alpha^2 theta >= 1, n <= 30d, n <= p)`, PATCH, ok, r ? `d = 2^${r.d.toString(2).length - 1}, n <= ${r.nMax}` : "k eps not an integer"));
  }
  out.push(
    truth(OBS, "b >= 64 d^2 eventually: b >= 2^(6/(1-2eps))", PATCH, true, `b >= 2^${toDecimal(cutoff64d2(p.epsilon), 4)}`, "observation"),
    truth(OBS, "b >= 96 d eventually: b >= 2^(7/(1-eps))", PATCH, true, `b >= 2^${toDecimal(cutoff96d(p.epsilon), 4)}`, "observation"),
  );

  // ---- 7H: the next ceiling (scoped) and comparisons
  const SH = "PR7-H scoped ceiling kappa < a/2 and comparisons";
  const a2 = div(p.a, q(2n));
  out.push(
    fromCheck(SH, { name: "kappa < min{g2, g3, g4} <= a min{eps, 1-eps} <= a/2", source: "PR5 fast-gaussian-note.tex, The next ceiling", lhs: p.kappa, rel: "<", rhs: a2, kind: "implied" }),
    truth(OBS, "kappa / (a/2)", "derived", true, toDecimal(div(p.kappa, a2), 6), "observation"),
    truth(OBS, "kappa / (83/10^12) (the repository head) and kappa / (1624/10^12) (PR 6)", "derived", true, `${toDecimal(div(p.kappa, q(83n, TEN(12))), 4)} and ${toDecimal(div(p.kappa, q(1624n, TEN(12))), 4)}`, "observation"),
  );

  // ---- 7T: text errata (observations)
  const staleC1 = q(49961n, 10000n);
  out.push(
    truth(
      "PR7-T stated constants in the patch text",
      `ERRATUM prime-field28.patch line 264: "C_1=49961/10000, so eps C_1<1" holds at this eps`,
      "prime-field28.patch 08-assembly \"Precision and exact recovery\" (inherited from PR 5's patch line 263)",
      lt(mul(p.epsilon, staleC1), ONE),
      `eps * 49961/10000 = ${show(mul(p.epsilon, staleC1))} (${toDecimal(mul(p.epsilon, staleC1), 6)}) > 1; with eq:fixed-parameters' C_1 = ${show(p.C1)}: ${toDecimal(mul(p.epsilon, p.C1), 6)} < 1`,
      "observation",
    ),
    truth("PR7-T stated constants in the patch text", "the example \"d = floor(b^(4999/10000))\" now uses this eps (PR 5's stale 19999/100000 corrected)", "prime-field28.patch line 145", eq(q(4999n, 10000n), p.epsilon), "", "observation"),
  );

  // ---- second route to the global count (optional, about 40 s more)
  if (opts.observation) {
    const fp = cached("pr7 fingerprint", () => fingerprintCount(H, computeLocal7().graph));
    out.push(truth(OBS, "second route: distinct 128-bit additive fingerprints of all local additions over the 378 contexts", "derived (pseudo-random lanes; for random lanes the chance of any collision would be about 2^-82)", fp.distinct === G.unique, `${fp.distinct} distinct (exact-key count ${G.unique})`, "observation"));
  }

  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { params: p, local: loc, global: G, bit: bn, logm, enclosure: enc, complexCircuit: cc, complex: cn, logmc, enclosurec: encc, gates, guard: gu, margins: mg, G: Gm, exponents: x, matching: mt, span, Rmax, RcMax } };
}
