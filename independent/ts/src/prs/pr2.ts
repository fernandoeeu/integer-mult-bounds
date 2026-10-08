// PR 2 (Andrew Barnes): "Aligned paired circuits for a conditional 17*2^-63 saving".
// Sources: notes/aligned-paired-note.tex and notes/aligned-paired-review.tex at prs/2
// (base bcd4ebd).
//
// Top-down: the local paired circuit (9813 additions, n = 49) is unchanged; only
// the labelling of each common-point group changes, so that complete root pairs
// agree across groups and more fixed-pair star sums are shared. The merged graph
// shrinks from c = 450394 to c = 435450 additions, R = c + q from 509194 to
// 494250. The bit network formulas of prop:paired-bit-interface then give
// eta_b = 23/642375000 and certify a = 305/10^11 (was 296/10^11). The 2^-59
// parameter recipe (beta = 999/1000, eps = 199/1000, delta = 1/10^4, C1 = 2) is
// kept with the new a, giving G = eps beta a^2 = 739738521/(4*10^26) > 17*2^-63.

import { type Q, q, sub, mul, div, eq, lt, twoPow, ONE, show, toDecimal } from "../rational";
import { margins, minimumMargin, parameterChecks, recipeParams, type Params } from "../parameters";
import { ground, complexNetwork, pairedBitNetwork } from "../networks";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { guardChecks, guardConstants } from "../guard";
import { gaussianChecks, gaussianInstance } from "../gaussian";
import { fixedNetworkCeiling, maxSideRoles, largestGridSaving } from "../ceiling";
import { buildPairedCircuit, PUBLISHED_CONVENTIONS, ALTERNATIVE_CONVENTIONS, type Circuit } from "../circuit";
import { verifyLocalCircuit } from "../verifyCircuit";
import { depthSamples } from "../checks";
import { alignedLabelling, labellingIsValid, mergeWith, pruneMerged, rootPairImages, verifyMerged, type MergedGraph } from "./aligned";
import { tripleIndex } from "../global";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const NOTE = "PR2 aligned-paired-note.tex";
const REVIEW = "PR2 aligned-paired-review.tex";
const H = 50;

export const STATED_PR2 = {
  localAdditions: 9813,
  localOutputs: 1176,
  c: 435450,
  q: 58800,
  R: 494250n,
  fewerThanPreceding: 14944, // review: "14,944 fewer additions than the preceding paired graph"
  precedingC: 450394, // published c (B1 of `bun run check`)
  W: 394839648000000n,
  s: 49354954232864000000n,
  D: 1767136000000n,
  eta: q(23n, 642375000n),
  L0: q(11737n, 1000n),
  a: q(305n, TEN(11)),
  ac: q(1n, TEN(11)),
  G: q(739738521n, 400000000000000000000000000n),
  kappa: q(17n, 1n << 63n),
  gammaExponent: q(1597n, 2000n),
};

export function pr2Params(a: Q = STATED_PR2.a, kappa: Q = STATED_PR2.kappa, ac: Q = STATED_PR2.ac): Params {
  return { ...recipeParams(a, ac), kappa };
}

/**
 * c by support identity instead of merge keys (second derivation): the number of distinct
 * global supports among all (group, local addition) pairs. Supports are compared through a
 * 128-bit Zobrist hash (four 32-bit lanes of fixed pseudo-random values per triple). Supports
 * of an addition are disjoint unions, so its hash is the lane-wise sum of its children's.
 * A collision can only merge two distinct supports, so it can only LOWER this count.
 */
export function distinctSupports(local: Circuit, h: number, L: number[][]): number {
  const n = h - 1;
  const P = local.inputs;
  const T = (h * (h - 1) * (h - 2)) / 6;
  let seed = 0x9e3779b9;
  const rnd = () => {
    // xorshift32, fixed seed: deterministic
    seed ^= seed << 13;
    seed >>>= 0;
    seed ^= seed >>> 17;
    seed ^= seed << 5;
    return (seed >>>= 0);
  };
  const Z = Array.from({ length: 4 }, () => Uint32Array.from({ length: T }, rnd));
  const pairs: [number, number][] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) pairs.push([a, b]);
  const seen = new Set<string>();
  const lanes = Array.from({ length: 4 }, () => new Uint32Array(P + local.left.length));
  for (let i = 0; i < h; i++) {
    const g = (u: number) => L[i]![u]!;
    for (let k = 0; k < P; k++) {
      const t = tripleIndex(h, [i, g(pairs[k]![0]), g(pairs[k]![1])]);
      for (let z = 0; z < 4; z++) lanes[z]![k] = Z[z]![t]!;
    }
    for (let k = 0; k < local.left.length; k++) {
      const id = P + k;
      for (let z = 0; z < 4; z++) lanes[z]![id] = (lanes[z]![local.left[k]!]! + lanes[z]![local.right[k]!]!) >>> 0;
      seen.add(`${lanes[0]![id]},${lanes[1]![id]},${lanes[2]![id]},${lanes[3]![id]}`);
    }
  }
  return seen.size;
}

export function computeAligned(opts: { alternative?: boolean } = {}) {
  return cached(`pr2 aligned ${opts.alternative ?? false}`, () => {
    const local = buildPairedCircuit(H - 1, PUBLISHED_CONVENTIONS);
    const localReport = verifyLocalCircuit(local);
    const L = alignedLabelling(H);
    const merged: MergedGraph = mergeWith(local, H, L);
    const pruned = pruneMerged(merged);
    const report = verifyMerged(pruned.graph);
    const bySupport = distinctSupports(local, H, L);
    let alt: ReturnType<typeof verifyMerged> | undefined;
    if (opts.alternative) {
      const altLocal = buildPairedCircuit(H - 1, ALTERNATIVE_CONVENTIONS);
      alt = verifyMerged(pruneMerged(mergeWith(altLocal, H, L)).graph);
    }
    return { localReport, labelling: L, beforePrune: merged.left.length, removed: pruned.removed, report, bySupport, roots: rootPairImages(H, L), alt };
  });
}

export type PR2Options = { p?: Params; stated?: Partial<typeof STATED_PR2>; alternative?: boolean; aligned?: ReturnType<typeof computeAligned> };

export function pr2(opts: PR2Options = {}) {
  const st = { ...STATED_PR2, ...opts.stated };
  const p = opts.p ?? pr2Params(st.a, st.kappa, st.ac);
  const out: Result[] = [];
  const A = opts.aligned ?? computeAligned({ alternative: opts.alternative });
  const rep = A.report;

  // ---- 2A: aligned relabelling and merged graph (rebuilt)
  const SA = "PR2-A aligned relabelling and merged graph at h = 50 (rebuilt from the note)";
  out.push(
    truth(SA, "every group's order is a bijection onto [50] minus {i}", NOTE, labellingIsValid(H, A.labelling)),
    truth(SA, "complete root pairs agree across groups: every local pair {2k,2k+1} maps to a global pair {2j,2j+1}", NOTE + ": All complete root pairs now agree", A.roots.allGlobalPairs, `${A.roots.distinct} distinct images`),
    equals(SA, "local additions (unchanged circuit)", NOTE, A.localReport.additions, st.localAdditions),
    equals(SA, "local outputs", NOTE, A.localReport.outputs, st.localOutputs, "identity"),
    equals(SA, "merged graph additions c", NOTE, rep.additions, st.c),
    equals(SA, "c by distinct global supports (second derivation: support identity via 128-bit Zobrist hash, not merge keys)", REVIEW + ", Finite claim F", A.bySupport, st.c),
    equals(SA, "additions removed by pruning after the merge", REVIEW + ": prune", A.removed, 0),
    equals(SA, "c reduction against the published graph: 450394 - c = 14944", REVIEW, st.precedingC - rep.additions, st.fewerThanPreceding),
    equals(SA, "partial outputs q = h C(h-1,2)", NOTE, rep.partialOutputs, st.q, "identity"),
    equals(SA, "R = c + q side roles (identity applied to the recomputed c)", REVIEW + ": R = C + Q = 494250", BigInt(rep.roles), st.R, "identity"),
    truth(SA, "every merged addition joins disjoint supports", REVIEW + ", Finite claim F", rep.allAdditionsDisjoint),
    truth(SA, "every partial output y_{i,T} = sum_{S cap T = {i}} x_S exactly (through merged decompositions)", REVIEW + ", Finite claim F", rep.allPartialOutputsExact),
    truth(SA, "every node's triples share a common point", NOTE + ": Every retained sum still has a common point", rep.everyNodeHasCommonPoint),
    truth(SA, "every node has an outgoing use", REVIEW, rep.everyNodeUsed, `${rep.inputsUsed} inputs used`),
    truth(SA, "every output triple meets its target in one point (implied by exactness)", REVIEW, rep.outputsMeetTargetInOnePoint, "", "implied"),
  );
  if (A.alt)
    out.push(
      truth("PR2-0 observation (not part of the claim)", "aligned labelling with the other reading of the circuit prose (ceil split, zeros dropped, weights first)", "README, Conventions", A.alt.allPartialOutputsExact && A.alt.allAdditionsDisjoint && A.alt.everyNodeHasCommonPoint && A.alt.everyNodeUsed, `c = ${A.alt.additions}, R = ${A.alt.roles}`, "observation"),
    );

  // ---- 2B: bit network and its saving
  const SB = "PR2-B bit network counts and a = 305/10^11";
  const g = ground(H);
  const bp = pairedBitNetwork(H, BigInt(rep.roles));
  const logm = cached("pr2 logm", () => logIntegerEnclosure(g.m, 24));
  const expL0 = cached(`pr2 exp ${show(st.L0)}`, () => expLowerBound(st.L0, 80));
  out.push(
    equals(SB, "W = 2N + 2v^2(R+h)", NOTE, bp.W, st.W),
    equals(SB, "s = Wm - N + 2L, L = 3 v^2 h^2", NOTE, bp.s, st.s),
    equals(SB, "D = Wm - s", NOTE, bp.deficit, st.D),
    equals(SB, "eta_b = D/(Wm)", NOTE, bp.eta, st.eta),
    fromCheck(SB, { name: "log m < 11737/1000 (atanh, 24 terms)", source: NOTE, lhs: logm.upper, rel: "<", rhs: st.L0 }),
    truth(SB, "e^(11737/1000) > m (Taylor partial sum, second route)", NOTE, lt(q(g.m), expL0)),
    fromCheck(SB, { name: "eta_b > a L0, a = 305/10^11", source: NOTE, lhs: mul(st.a, st.L0), rel: "<", rhs: bp.eta }),
    equals(SB, "largest bit saving on the 10^-11 grid allowed by eta_b > a L0", "derived", largestGridSaving(bp.eta, st.L0, TEN(11)), 305n),
    truth(SB, "R within the role budget for a = 305/10^11", "derived from prop:paired-bit-interface", BigInt(rep.roles) <= maxSideRoles(H, st.a, st.L0), `largest admissible R = ${maxSideRoles(H, st.a, st.L0)}`),
    fromCheck(SB, { name: "1 - tau <= a = 305/10^11", source: NOTE + ": tau = 1 - a", lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
  );

  // ---- 2C: unchanged complex network (h = 50)
  const SC = "PR2-C complex network unchanged (h = 50), a_c = 1/10^11";
  const cx = complexNetwork(H);
  out.push(fromCheck(SC, { name: "eta_c > a_c L0", source: NOTE + ": complex motif and saving unchanged", lhs: mul(p.ac, st.L0), rel: "<", rhs: cx.eta }));
  out.push(truth(SC, "2 L_c < N (complex residual construction; the PR's script requires it)", "aligned_paired_network.py require", 2n * cx.L < g.N, "", "implied"));

  // ---- 2D: parameters and margins
  const SD = "PR2-D parameters (2^-59 recipe at a = 305/10^11) and final margin";
  const mg = margins(p);
  const G = minimumMargin(p);
  out.push(...parameterChecks(p).map((k) => fromCheck(SD, k)));
  out.push(
    equals(SD, "G = min g_j = 739738521/(4*10^26)", NOTE, G, st.G),
    truth(SD, "G = g2 = g3 = eps beta a^2", NOTE, eq(G, mg.g2) && eq(G, mg.g3) && eq(G, mul(mul(p.epsilon, p.beta), mul(p.a, p.a)))),
    fromCheck(SD, { name: "17 * 2^-63 < G", source: NOTE, lhs: st.kappa, rel: "<", rhs: G, kind: "implied" }),
    equals(SD, "kappa / 2^-59 = 17/16", NOTE + ": improves the preceding 2^-59 headline by 17/16", mul(p.kappa, twoPow(59)), q(17n, 16n)),
  );

  // ---- 2E: guard and Gaussian, unchanged
  const SE = "PR2-E stopped guard and Gaussian width (unchanged inputs)";
  const gc = guardConstants(cx.W, cx.s, g.m);
  out.push(...guardChecks(cx.W, cx.s, g.m, p.beta, p.C1).map((k) => fromCheck(SE, k)));
  const depth = cached(`pr2 depth ${show(p.beta)}`, () => depthSamples(g.m, cx.s, gc.E, gc.B, p.beta));
  out.push(truth(SE, "unrolled depth recurrence obeys both stated bounds on all samples", "stopped-guard.tex", depth.ok, depth.detail));
  out.push(...gaussianChecks(p.epsilon, st.gammaExponent, NOTE + ": Gaussian width and b >= 2^40 cutoff retained", 46n).map((k) => fromCheck(SE, k)));
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`gauss ${e} ${show(p.epsilon)}`, () => gaussianInstance(e, p.epsilon));
    out.push(truth(SE, `b = 2^${e}: alpha, gamma meet every stated bound`, NOTE, r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }

  // ---- 2F: room left (the PR's certificate field fixed_network_ceiling)
  const SF = "PR2-F fixed-network ceiling";
  const ceil = fixedNetworkCeiling(bp.eta, logm.lower);
  out.push(truth(SF, "a_up^2 / (5(1 - a_up)) < 2^-58 for this aligned graph", "aligned_paired_network.py / certificate fixed_network_ceiling", lt(ceil.value, twoPow(-58)), `ceiling / 2^-59 = ${toDecimal(div(ceil.value, twoPow(-59)), 6)}`));

  return { results: out, values: { aligned: A, bit: bp, logm, params: p, margins: mg, G, complex: cx, guard: gc, ceiling: ceil } };
}

