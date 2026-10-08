// PR 6 (eumemic): "An aligned bit circuit with cheaper centers and a conditional
// integer-multiplication saving 1624/10^12". Head 5015011, base 6e56487; it
// contains PR 5 (d3d370c, which contains PR 3) plus one commit. Sources:
// notes/aligned-bit-note.tex, notes/aligned-bit-construction.tex,
// docs/research/aligned-bit.md, patches/aligned-bit-30.patch.
//
// Top-down: only the bit network at h = 50 changes.
//  (1) side circuit: blocks {2k, 2k+1} at every level in every group (partner of
//      the common point a singleton), top-level pair-star leave-one-block-out sums
//      by one prefix/suffix chain per pair {i, q} shared by groups i and q, and a
//      group total z_i kept per group: c = 435346 additions (totals included),
//      q = 58800 partial outputs, h = 50 center roles, R = c + q + h = 494196;
//  (2) centers: each center wire carries z_i out of the side graph, so it loses
//      h - 1 dimensions instead of h: L = 3 v^2 h(h-1).
// Then W = 2N + 2v^2 R, s = Wm - N + 6 v^2 h(h-1), eta_b = 49/1284490000,
// a = 325/10^11. The fast-Gaussian assembly of PR 5 is reused with tau = 1 - a,
// lambda = 1 - 32495/10^13, lambda' = 1 - 3249/10^12, kappa = 1624/10^12.
// The frame argument for (2) is a written proof, not checked here.

import { q, add, sub, mul, div, lt, eq, twoPow, ONE, show, toDecimal } from "../rational";
import { ground, pairedBitNetwork } from "../networks";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { largestGridSaving } from "../ceiling";
import { PUBLISHED_CONVENTIONS } from "../circuit";
import { computeCircuit3, compressedNetwork } from "./pr3";
import { pr5Params, errataRows } from "./pr5";
import { fastParameterChecks, fastMargins, fastMinimumMargin, guardBetaThreshold, leafAndGuardCompatible } from "./fastGaussian";
import { mergeGroups, verifyAlignedBit, PR6_OPTIONS } from "./alignedBit";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const NOTE = "PR6 aligned-bit-note.tex";
const CON = "PR6 aligned-bit-construction.tex";
const DOC = "PR6 aligned-bit.md";
const H = 50;

export const STATED_PR6 = {
  c: 435346,
  q: 58800,
  centers: 50,
  R: 494196n,
  publishedRoles: 509244n,
  W: 394759742720000n,
  s: 49344965957616000000n,
  D: 1882384000000n,
  eta: q(49n, 1284490000n),
  L0: q(11737n, 1000n),
  a: q(325n, TEN(11)),
  previousEta: q(23n, 661055000n),
  numerator: 4900n, // v - 6h(h-1)
  previousNumerator: 4600n, // v - 6h^2
  leafValue: q(336n, TEN(11)), // (1 - beta) a_c = 3.36 * 10^-9
  G: q(162446751n, TEN(17)),
  gap: q(46751n, TEN(17)),
};

export function pr6Params(): CompactParams {
  const p = pr5Params();
  const a = q(325n, TEN(11));
  return { ...p, a, tau: sub(ONE, a), lambda: sub(ONE, q(32495n, TEN(13))), lambdaPrime: sub(ONE, q(3249n, TEN(12))), kappa: q(1624n, TEN(12)) };
}

/** The aligned bit network with cheaper centers (prop:aligned-bit-interface). */
export function alignedBitNetwork(h: number, R: bigint) {
  const { v, N, m, h: H_ } = ground(h);
  const W = 2n * N + 2n * v * v * R;
  const L = 3n * v * v * H_ * (H_ - 1n);
  const s = W * m - N + 2n * L; // = Wm - N + 6 v^2 h(h-1)
  const D = W * m - s;
  return { v, N, m, W, L, s, D, eta: q(D, W * m) };
}

/** Largest R with eta(R) > a L0 for the aligned network: v + R < D / (2 v^2 m a L0). */
export function alignedRoleBudget(h: number, a: ReturnType<typeof q>, L0: ReturnType<typeof q>): bigint {
  const { v, N, m, h: H_ } = ground(h);
  const D = N - 6n * v * v * H_ * (H_ - 1n);
  const bound = sub(div(q(D), mul(q(2n * v * v * m), mul(a, L0))), q(v));
  const fl = bound.num / bound.den;
  return fl * bound.den === bound.num ? fl - 1n : fl;
}

export function computeAligned6(alternative = false) {
  const main = cached("pr6 aligned", () => {
    const G = mergeGroups(H, PR6_OPTIONS);
    return { graph: G, report: verifyAlignedBit(G) };
  });
  const alt = alternative ? cached("pr6 aligned published conventions", () => mergeGroups(H, { ...PR6_OPTIONS, conv: PUBLISHED_CONVENTIONS })) : null;
  return { ...main, alt };
}

export type PR6Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR6>; alternative?: boolean };

export function pr6(opts: PR6Options = {}) {
  const st = { ...STATED_PR6, ...opts.stated };
  const p = opts.p ?? pr6Params();
  const out: Result[] = [];
  const A = computeAligned6(opts.alternative ?? false);
  const rep = A.report;
  const g = ground(H);

  // ---- 6A: the side circuit (rebuilt)
  const SA = "PR6-A aligned side circuit at h = 50 with shared chains and totals (rebuilt)";
  const R = BigInt(rep.additions + rep.partialOutputs + rep.totalsCount);
  out.push(
    equals(SA, "additions c (totals included, after pruning)", CON + ": c = 435346", rep.additions, st.c),
    equals(SA, "partial outputs q", CON, rep.partialOutputs, st.q),
    equals(SA, "group totals (center sources)", CON, rep.totalsCount, st.centers),
    truth(SA, "every partial output exact: y_{i,T} = sum over S with S cap T = {i}", CON + ": Exact support comparison checks every partial output", rep.allPartialOutputsExact),
    truth(SA, "every total exact: z_i = all triples containing i, the 50 totals distinct", CON + ": and total", rep.totalsExact && rep.distinctTotals),
    truth(SA, "every addition joins disjoint supports (partial-output and total subtrees)", CON, rep.allAdditionsDisjoint && rep.totalsDisjoint),
    truth(SA, "every node reached from group i has common point i", CON + ": the common point of every node", rep.everyNodeHasCommonPoint),
    truth(SA, "every addition is used (by an addition, a partial output or a total)", CON, rep.everyNodeUsedWithTotals),
    equals(SA, "R = c + q + h (the compiler identity applied to the recomputed counts)", CON + ": R = c + q + h = 494196", R, st.R, "identity"),
    equals(SA, "published roles 509244 = 509194 + 50 (old R + h center wires)", NOTE, 509194n + 50n, st.publishedRoles, "identity"),
    truth("PR6-0 observations (not part of the claim)", "cross-group identifications (local additions merged into an earlier group's node)", CON, true, `${A.graph.mergedAdditions}; per-group local additions ${Math.min(...A.graph.localAdditions)}..${Math.max(...A.graph.localAdditions)}`, "observation"),
  );
  if (A.alt)
    out.push(
      truth(
        "PR6-0 observations (not part of the claim)",
        "the same construction under the published summation conventions (zero terms kept in the split)",
        CON + ': "the rest of the recursion is unchanged"',
        true,
        `c = ${A.alt.left.length}, R = ${A.alt.left.length + 58800 + 50}; certified saving ${largestGridSaving(alignedBitNetwork(H, BigInt(A.alt.left.length + 58800 + 50)).eta, st.L0, TEN(11))}/10^11`,
        "observation",
      ),
    );

  // ---- 6B: the bit network
  const SB = "PR6-B aligned bit network with cheaper centers: counts, eta_b, a = 325/10^11";
  const nw = alignedBitNetwork(H, R);
  const logm = cached("pr6 logm", () => logIntegerEnclosure(g.m, 24));
  const expL0 = cached(`pr6 exp ${show(st.L0)}`, () => expLowerBound(st.L0, 60));
  const enc = savingEnclosure(nw.eta, logm);
  out.push(
    equals(SB, "W = 2N + 2v^2 R", CON + " prop:aligned-bit-interface", nw.W, st.W),
    equals(SB, "s = Wm - N + 6 v^2 h(h-1)", CON, nw.s, st.s),
    equals(SB, "Wm - s = N - 6 v^2 h(h-1)", CON, nw.D, st.D),
    equals(SB, "eta_b = 49/1284490000", CON, nw.eta, st.eta),
    equals(SB, "previous eta_b of the paired network (R = 509194, recomputed by B1 of `bun run check`) = 23/661055000", CON + ": against 23/661055000 for the paired network", pairedBitNetwork(H, 509194n).eta, st.previousEta),
    equals(SB, "numerator v - 6h(h-1) = 4900 (was v - 6h^2 = 4600)", DOC, g.v - 6n * 50n * 49n, st.numerator),
    equals(SB, "previous numerator v - 6h^2 = 4600", DOC, g.v - 6n * 2500n, st.previousNumerator, "identity"),
    equals(SB, "eta_b = (v - 6 h(h-1)) / (2 m (v + R)) (the doc's formula)", DOC, q(g.v - 6n * 50n * 49n, 2n * g.m * (g.v + R)), nw.eta, "identity"),
    fromCheck(SB, { name: "log m < 11737/1000 (atanh, 24 terms)", source: CON, lhs: logm.upper, rel: "<", rhs: st.L0 }),
    truth(SB, "e^(11737/1000) > m (Taylor partial sum, second route)", CON, lt(q(g.m), expL0)),
    fromCheck(SB, { name: "eta_b > (325/10^11)(11737/1000)", source: CON, lhs: mul(st.a, st.L0), rel: "<", rhs: nw.eta }),
    truth(SB, "a < lower enclosure of the actual saving -log(1 - eta_b)/log m (Mercator route)", CON, lt(st.a, enc.lower), `a* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    fromCheck(SB, { name: "1 - tau <= a = 325/10^11", source: NOTE, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    fromCheck(SB, { name: "1 - sigma <= a_c = 14/10^9 (complex network unchanged from PR 3)", source: NOTE, lhs: sub(ONE, p.sigma), rel: "<=", rhs: q(14n, TEN(9)), kind: "condition" }),
    truth("PR6-0 observations (not part of the claim)", "largest bit saving on the 10^-11 grid; role budget for 326/10^11", CON, true, `${largestGridSaving(nw.eta, st.L0, TEN(11))}/10^11; 326 would need R <= ${alignedRoleBudget(H, q(326n, TEN(11)), st.L0)} (have ${R})`, "observation"),
  );

  // ---- 6C: assembly (PR 5's system with the new tau)
  const SC = "PR6-C fast-Gaussian assembly with tau = 1 - 325/10^11";
  const x = layerExponents(p);
  const mg = fastMargins(p);
  const G = fastMinimumMargin(p);
  out.push(...fastParameterChecks(p).map((k) => fromCheck(SC, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SC, { name: `kappa < ${k}`, source: NOTE + " (PR 5's eq:margin-list)", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SC, "sigma < tau, so chi = tau", NOTE, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SC, "(1 - beta) a_c = 3.36 * 10^-9", NOTE, mul(sub(ONE, p.beta), p.ac), st.leafValue),
    fromCheck(SC, { name: "(1 - beta) a_c > 1 - lambda' (the leaf)", source: NOTE, lhs: sub(ONE, p.lambdaPrime), rel: "<", rhs: mul(sub(ONE, p.beta), p.ac), kind: "implied" }),
    fromCheck(SC, { name: "beta > 3/4 (the guard; same as eps C1 < 1 here)", source: NOTE, lhs: guardBetaThreshold(p), rel: "<", rhs: p.beta, kind: "implied" }),
    equals(SC, "G_* = g3", NOTE, G, mg.g3),
    equals(SC, "G_* = 162446751/10^17", NOTE, G, st.G),
    equals(SC, "G_* - kappa = 46751/10^17", "certificate absorption_gap (the note states only G_* > kappa)", sub(G, p.kappa), st.gap),
    fromCheck(SC, { name: "kappa > 2^-30", source: NOTE, lhs: twoPow(-30), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SC, { name: "kappa < 2^-29", source: NOTE, lhs: p.kappa, rel: "<", rhs: twoPow(-29), kind: "condition" }),
    fromCheck(SC, { name: "scoped ceiling: kappa < a/2 < 2^-29", source: NOTE, lhs: div(p.a, q(2n)), rel: "<", rhs: twoPow(-29), kind: "constant" }),
    fromCheck(SC, { name: "kappa < g3 < eps a <= a/2", source: NOTE, lhs: mg.g3, rel: "<", rhs: div(p.a, q(2n)), kind: "implied" }),
  );
  // "A further 3% on a_b would close this window" (doc): where the leaf-and-guard window closes
  const closeFixedBeta = mul(sub(ONE, p.beta), p.ac); // a must stay below (1 - beta) a_c at kappa ~ a/2
  const closeBestBeta = mul(sub(ONE, guardBetaThreshold(p)), p.ac);
  out.push(
    truth(
      "PR6-0 observations (not part of the claim)",
      'the doc: "A further 3% on a_b would close this window" (leaf (1-beta) a_c > 1 - lambda\' ~ a, guard beta > 3/4)',
      DOC,
      true,
      `at beta = 19/25 the window closes at a = ${toDecimal(mul(closeFixedBeta, q(TEN(11))), 2)}/10^11 (+${toDecimal(mul(sub(div(closeFixedBeta, p.a), ONE), q(100n)), 1)}%); at the guard threshold beta -> ${toDecimal(guardBetaThreshold(p), 6)} it closes at ${toDecimal(mul(closeBestBeta, q(TEN(11))), 2)}/10^11 (+${toDecimal(mul(sub(div(closeBestBeta, p.a), ONE), q(100n)), 1)}%)`,
      "observation",
    ),
    truth("PR6-0 observations (not part of the claim)", "kappa / (1479/10^12) = 56/51", "certificate improvement_over_fast_gaussian", eq(div(p.kappa, q(1479n, TEN(12))), q(56n, 51n)), "", "observation"),
  );

  // ---- 6D: guard (complex network and beta unchanged from PR 5)
  const SD = "PR6-D generalized guard (compressed complex network, beta = 19/25; as PR 5)";
  const c3 = computeCircuit3();
  const cx = compressedNetwork(25, BigInt(c3.additions + c3.injections));
  const gu = compactGuardConstants(cx.W, cx.s, cx.m, p.zeta);
  out.push(...compactGuardChecks(cx.W, cx.s, cx.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SD, k)));
  const depth = cached(`pr5 depth ${show(p.beta)} ${cx.s}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], cx.m, cx.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SD, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));
  out.push(truth(SD, "the resampling lemmas and Gaussian width are PR 5's (counted under PR 5, not repeated here)", NOTE, leafAndGuardCompatible(p, p.ac), "", "implied"));

  // ---- 6T: errata carried over from PR 5's text
  out.push(...errataRows("PR6-T stated constants in the patch text", p, "aligned-bit-30.patch", 266, 218));

  const OBS = "PR6-0 observations (not part of the claim)";
  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { aligned: A, network: nw, R, logm, enclosure: enc, guard: gu, complex: cx, params: p, exponents: x, margins: mg, G } };
}
