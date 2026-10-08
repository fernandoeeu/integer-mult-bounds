// PR 14 (Rohan Arun): "Combine source frames with h30 data-corner batching". Head 1fa5b9a,
// one commit on top of PR 12's head 35d31e3 (so it contains PR 12, PR 10, and through them
// PR 7, 9, 11 byte-identically). It adds research/controlled-corners/ (a held-back local
// result) and research/source-frame-corners/ (the headline), with a pinned copy of PR 13's
// notes and certificate under research/source-frame-corners/pr13/.
// Sources: research/source-frame-corners/README.md, proof.tex, complex.tex;
// research/controlled-corners/README.md, proof.tex.
//
// Top-down. Bit network: PR 12's h = 30 producer unchanged (R = 17515487, v = 142506,
// m = 27000, H = 900). Child list per edge class:
//   stage 1-3 join (B = v^2 R copies, rank m - 2h):   2h = 60 singletons, block m - 4h = 26880
//   stage 2 exit with PR 13's source frame (B, rank m - h): h = 30 singletons, block m - 2h = 26940
//   stage 3 data entrance (2N, rank (H-1)(h-1) = 26071): 3r = 87 singletons (r = h - 1),
//       blocks H - 2r = 842 (new, data corner) and m - 2(H + r) = 25142
//   stage 2 data entrance (2N, rank (h-1)^2 = 841): 2h - 1 = 59 singletons, block H - 4h + 2 = 782 (new)
// S = s - B(26880 + 26940) - 2N(25142 + 842 + 782) = 65379670780393117512, a_b = 1816/10^9.
// Complex network: PR 13's three whole-residual classes at h = 28, unchanged; a sharper
// exponent a_c = 18179/10^10 from the same bound; leaf (1 - beta) a_c > a_b.
// Assembly: PR 13's system with kappa = 90799/10^11.
// The held-back sub-claim (controlled-corners) uses PR 12's sink blocks plus an entrance
// block of 840 and the two data blocks with PR 10's complex network: a_b = 40315/10^11,
// kappa = 5039/(25*10^9). It is superseded in the PR by the headline but is checked too.

import { q, add, sub, mul, div, lt, twoPow, ONE, show, toDecimal, type Q } from "../rational";
import { type CompactParams } from "../compact/witness";
import { primeFieldBitNetwork, primeFieldComplexNetwork, computeComplex7 } from "./pr7";
import { momentWeights, momentUpperBound, momentUpperSecond, momentLower, largestGridSaving, type WidthClass } from "./batched";
import { batchedAssemblyRows, logBoundRows, guardRows, STATED_PR10, ANALYTIC_PR10 } from "./pr10";
import { STATED_PR12 } from "./pr12";
import { STATED_PR13 } from "./pr13";
import { roundedLogUp, roleBudget, largestGridConservative } from "./allResiduals";
import { equals, truth, fromCheck, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const SFC = "PR14 research/source-frame-corners/proof.tex";
const SFR = "PR14 research/source-frame-corners/README.md";
const CPX = "PR14 research/source-frame-corners/complex.tex";
const CC = "PR14 research/controlled-corners/proof.tex";
const CCR = "PR14 research/controlled-corners/README.md";
const H30 = 30n;

export const STATED_PR14 = {
  R: 17515487n,
  singles: [60n, 30n, 87n, 59n],
  ranks: [26940n, 26970n, 26071n, 841n],
  widths: "26880;26940;25142,842;782",
  S: 65379670780393117512n,
  a: q(1816n, TEN(9)),
  gapDecimal: q(19154n, TEN(14)),
  ac: q(18179n, TEN(10)),
  cGapDecimal: q(21196n, TEN(15)),
  leafSaving: q(18160821n, TEN(13)),
  agap: q(40919500001n, 5n * TEN(21)),
  agapDecimal: q(81839n, TEN(16)),
  overPR13pct: [q(179355n, 10000n), q(179365n, 10000n)] as [Q, Q], // "17.936%"
  // held-back controlled-corners sub-claim
  ccA: q(40315n, TEN(11)),
  ccGapDecimal: q(14n, TEN(13)),
  ccKappa: q(5039n, 25000000000n),
  ccEps: q(99999979n, 200000000n),
  ccAgap: q(14957569250021n, TEN(24)),
  ccOverPR12pct: [q(59345n, 1000n), q(59355n, 1000n)] as [Q, Q], // "59.35%"
};

const paramsFor = (a: Q, ac: Q, eps: Q, kappa: Q): CompactParams => {
  const tau = sub(ONE, a);
  return {
    a,
    ac,
    tau,
    sigma: sub(ONE, ac),
    epsilon: eps,
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(10)),
    C1: q(11999n, 10000n),
    lambda: add(tau, q(1n, TEN(16))),
    lambdaPrime: add(tau, q(2n, TEN(16))),
    kappa,
  };
};
export const pr14Params = () => paramsFor(STATED_PR14.a, STATED_PR14.ac, q(499999n, TEN(6)), q(90799n, TEN(11)));
export const pr14ccParams = () => paramsFor(STATED_PR14.ccA, STATED_PR10.ac, STATED_PR14.ccEps, STATED_PR14.ccKappa);

/** The headline child list (order as in the certificate: join, stage-3 middle, exit, stage-3 corner, stage-2 data). */
export function pr14Classes(h: bigint, v: bigint, R: bigint): WidthClass[] {
  const m = h ** 3n;
  const H = h * h;
  const r = h - 1n;
  const B = v * v * R;
  const N2 = 2n * v ** 3n;
  return [
    { name: "stage 1-3 join block m - 4h", copies: B, t: m - 4n * h },
    { name: "stage 3 data entrance middle block m - 2(H + r)", copies: N2, t: m - 2n * (H + r) },
    { name: "stage 2 source-frame exit block m - 2h", copies: B, t: m - 2n * h },
    { name: "stage 3 data entrance corner block H - 2r", copies: N2, t: H - 2n * r },
    { name: "stage 2 data entrance block H - 4h + 2", copies: N2, t: H - 4n * h + 2n },
  ];
}

/** The held-back controlled-corners child list (PR 12's sink blocks H and m - 2H, entrance H - 2h, two data blocks). */
export function pr14ccClasses(h: bigint, v: bigint, R: bigint): WidthClass[] {
  const m = h ** 3n;
  const H = h * h;
  const r = h - 1n;
  const B = v * v * R;
  const N2 = 2n * v ** 3n;
  return [
    { name: "stage 1-3 join block m - 4h", copies: B, t: m - 4n * h },
    { name: "stage 2 sink middle block m - 2H", copies: B, t: m - 2n * H },
    { name: "stage 3 data entrance middle block", copies: N2, t: m - 2n * (H + r) },
    { name: "stage 2 sink corner block H", copies: B, t: H },
    { name: "stage 2 auxiliary entrance block H - 2h", copies: B, t: H - 2n * h },
    { name: "stage 3 data entrance corner block H - 2r", copies: N2, t: H - 2n * r },
    { name: "stage 2 data entrance block H - 4h + 2", copies: N2, t: H - 4n * h + 2n },
  ];
}

export function pr14(opts: { p?: CompactParams; pcc?: CompactParams; stated?: Partial<typeof STATED_PR14> } = {}) {
  const st = { ...STATED_PR14, ...opts.stated };
  const p = opts.p ?? pr14Params();
  const pcc = opts.pcc ?? pr14ccParams();
  const out: Result[] = [];
  const OBS = "PR14-0 observations and analytic steps (not counted)";

  // ---- 14A: bit network, source frames plus data corners
  const SA = "PR14-A h = 30 bit network with source-frame exit and two data blocks, a_b = 1816/10^9 (producer count taken from PR 12, not rebuilt)";
  const bn = primeFieldBitNetwork(30, st.R);
  const { m, v } = bn;
  const H = H30 * H30;
  const r = H30 - 1n;
  const ranks = [m - 2n * H30, m - H30, (H - 1n) * r, r * r];
  const singles = [2n * H30, H30, 3n * r, 2n * H30 - 1n];
  const cls = pr14Classes(H30, v, st.R);
  const w = momentWeights(m, bn.W, bn.s, cls);
  out.push(
    equals(SA, "R is PR 12's role count (entry 12; producer not rebuilt)", SFR, st.R, STATED_PR12.R, "identity"),
    equals(SA, "ranks: join m - 2h, exit m - h, stage-3 entrance (H-1)(h-1), stage-2 data entrance (h-1)^2", SFC + "; " + CC, ranks.join(","), st.ranks.join(",")),
    equals(SA, "singleton pivots 2h, h, 3(h-1), 2h - 1", SFC, singles.join(","), st.singles.join(",")),
    equals(SA, "block widths m - 4h; m - 2h; m - 2(H + h - 1), H - 2(h - 1); H - 4h + 2", SFC, `${cls[0]!.t};${cls[2]!.t};${cls[1]!.t},${cls[3]!.t};${cls[4]!.t}`, st.widths),
    truth(SA, "each class: singletons + blocks = rank", SFC, singles[0]! + cls[0]!.t === ranks[0] && singles[1]! + cls[2]!.t === ranks[1] && singles[2]! + cls[1]!.t + cls[3]!.t === ranks[2] && singles[3]! + cls[4]!.t === ranks[3]),
    truth(SA, "rank per stage-two role unchanged: (h^2 - h) + (m - h^2) = 0 + (m - h)", SFC, H30 * H30 - H30 + (m - H) === m - H30, "", "identity"),
    equals(SA, "S = s - B(26880 + 26940) - 2N(25142 + 842 + 782)", SFC, w.S, st.S),
    equals(SA, "S = S_1 - 840 B - 2N(842 + 782) (PR 12's S_1; equals the controlled-corners S_2)", CC, STATED_PR12.S1 - 840n * v * v * st.R - 2n * bn.N * (842n + 782n), st.S),
    equals(SA, "weights sum to 1 - 3857/52973979000 (rank sum unchanged)", SFC, w.total, sub(ONE, q(3857n, 52973979000n))),
    truth(SA, "every child width below m (strict contraction)", SFC, cls.every((c) => c.t < m)),
  );
  const ells = w.items.map((x) => roundedLogUp(x.r, TEN(10)));
  const b = momentUpperBound(w.items, st.a, ells);
  const b2 = momentUpperSecond(w.items, st.a);
  const gridB = cached("pr14 grid bit", () => largestGridSaving(w.items, TEN(9), 1816n));
  const gridCons = largestGridConservative(w.items, ells, TEN(9), 1816n);
  out.push(
    fromCheck(SA, { name: "Psi(1 - 1816/10^9) <= sum w_i/(1 - a l_i) < 1 (l_i: own enclosures rounded up to 10^-10)", source: SFC, lhs: b.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "certified gap > 1.9154*10^-10", source: SFR, lhs: st.gapDecimal, rel: "<", rhs: b.gap }),
    fromCheck(SA, { name: "second route: Psi(1-a_b) < 1 (own enclosures, sharper exponential bound)", source: "derived", lhs: b2.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "1 - tau <= a_b", source: SFR, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    truth(OBS, "room: largest a_b on the 10^-9 grid (second route; conservative route with the rounded logs)", "derived", true, `${gridB.k}/10^9 (Psi >= 1 from ${gridB.firstFail}/10^9); conservative ${gridCons}/10^9`, "observation"),
    truth(OBS, "certified bit gap with the rounded logs", "derived", true, toDecimal(b.gap, 16), "observation"),
  );
  // negative controls named by the README: dropping either data block fails at the chosen saving
  const without = (k: number) => momentLower(momentWeights(m, bn.W, bn.s, cls.filter((_, i) => i !== k)).items, st.a);
  out.push(
    truth(SA, "negative control: without the 842 block, Psi(1 - a_b) >= 1 already by e^x >= 1 + x", SFR, !lt(without(3), ONE)),
    truth(SA, "negative control: without the 782 block, Psi(1 - a_b) >= 1 already by e^x >= 1 + x", SFR, !lt(without(4), ONE)),
  );
  const Rmax = cached("pr14 Rmax", () => roleBudget(st.R, st.a, (R) => { const n = primeFieldBitNetwork(30, R); return { m: n.m, W: n.W, s: n.s, classes: pr14Classes(H30, n.v, R) }; }));
  out.push(truth(OBS, "role budget: largest R still certifying a_b = 1816/10^9 (second route)", "derived", true, `R <= ${Rmax}; PR 12's R = ${st.R} leaves ${Rmax - st.R} roles (${toDecimal(q(Rmax - st.R, st.R), 6)} of R)`, "observation"));

  // ---- 14B: complex network (PR 13's classes) with a sharper exponent
  const SB = "PR14-B complex network: PR 13's three whole-residual classes at h = 28, a_c = 18179/10^10";
  const cc = computeComplex7();
  const Rc = BigInt(cc.additions + cc.injections);
  const cn = primeFieldComplexNetwork(28, Rc);
  const Bc = cn.v * cn.v * (Rc + 29n);
  const d3 = (28n * 28n - 1n) * 27n;
  const cclasses: WidthClass[] = [
    { name: "whole residual rank m - 2h", copies: Bc, t: cn.m - 56n },
    { name: "whole residual rank m - h^2", copies: Bc, t: cn.m - 784n },
    { name: "stage-three data entrance", copies: 2n * cn.v ** 3n, t: d3 },
  ];
  const cw = momentWeights(cn.m, cn.W, cn.s, cclasses);
  const c = momentUpperBound(cw.items, st.ac, STATED_PR13.cLogs);
  const c2 = momentUpperSecond(cw.items, st.ac);
  const gridC = cached("pr14 grid c", () => largestGridSaving(cw.items, TEN(10), 18179n));
  const gridCc = largestGridConservative(cw.items, STATED_PR13.cLogs, TEN(10), 18179n);
  out.push(
    equals(SB, "S_c' as in PR 13 (unchanged construction)", CPX, cw.S, STATED_PR13.Sc),
    equals(SB, "rank-mass weights as in PR 13", CPX, cw.items.map((x) => show(x.w)).join(","), STATED_PR13.cw.map(show).join(",")),
    ...logBoundRows(SB, cw.items, STATED_PR13.cLogs, CPX + " (PR 13's displayed bounds, unchanged)"),
    fromCheck(SB, { name: "sum w_i/(1 - a_c l_i) < 1 at a_c = 18179/10^10 with PR 13's displayed l_i", source: CPX, lhs: c.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "gap > 2.1196*10^-11", source: CPX, lhs: st.cGapDecimal, rel: "<", rhs: c.gap }),
    fromCheck(SB, { name: "second route: Xi(1 - a_c) < 1", source: "derived", lhs: c2.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: CPX, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    equals(SB, "leaf saving (1 - beta) a_c = 18160821/10^13", CPX, mul(sub(ONE, p.beta), st.ac), st.leafSaving),
    fromCheck(SB, { name: "(1 - beta) a_c > a_b (sigma + beta(1 - sigma) < tau)", source: CPX, lhs: st.a, rel: "<", rhs: mul(sub(ONE, p.beta), st.ac) }),
    truth(OBS, "room: largest a_c on the 10^-10 grid (second route; conservative with PR 13's logs)", "derived", true, `${gridC.k}/10^10; conservative ${gridCc}/10^10`, "observation"),
  );
  const SC = "PR14-C depth guard (PR 13's, unchanged: three selected complex classes)";
  out.push(...guardRows(SC, cn.m, 28n, [cn.m - 56n, cn.m - 784n, d3], STATED_PR13.pathBounds, cn.W, cn.s, p, CPX, { qq: 22120n }));

  // ---- 14D: assembly
  const SD = "PR14-D assembly: eps = 499999/10^6, kappa = 90799/10^11";
  const asm = batchedAssemblyRows(SD, p, { gap: st.agap }, SFR);
  out.push(...asm.rows);
  const pct = mul(sub(div(p.kappa, q(7699n, TEN(10))), ONE), q(100n));
  out.push(
    fromCheck(SD, { name: "final absorption gap > 8.1839*10^-12", source: SFR, lhs: st.agapDecimal, rel: "<", rhs: sub(asm.G, p.kappa) }),
    truth(SD, "17.936% above PR 13's 7699/10^10 (rounds to 17.936)", SFR, !lt(pct, st.overPR13pct[0]) && lt(pct, st.overPR13pct[1]), toDecimal(pct, 5) + "%"),
    fromCheck(SD, { name: "kappa > 2^-21", source: "derived (dyadic bracket)", lhs: twoPow(-21), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < 2^-20 (PR 14 does not claim 2^-20)", source: "derived (dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-20), kind: "condition" }),
    truth(OBS, "kappa / (a_b/2)", "derived", true, toDecimal(div(p.kappa, div(st.a, q(2n))), 7), "observation"),
  );

  // ---- 14E: the held-back controlled-corners sub-claim (PR 10's complex network)
  const SE = "PR14-E held-back controlled-corners candidate: a_b = 40315/10^11, kappa = 5039/(25*10^9) (PR 10's complex network)";
  const ccl = pr14ccClasses(H30, v, st.R);
  const ccw = momentWeights(m, bn.W, bn.s, ccl);
  const ccE = ccw.items.map((x) => roundedLogUp(x.r, TEN(10)));
  const ccb = momentUpperBound(ccw.items, st.ccA, ccE);
  const ccb2 = momentUpperSecond(ccw.items, st.ccA);
  const gridCC = cached("pr14 grid cc", () => largestGridSaving(ccw.items, TEN(11), 40315n));
  out.push(
    equals(SE, "S_2 = S_1 - 840 B - (842 + 782) 2N", CC, ccw.S, st.S),
    equals(SE, "auxiliary entrance profile: h singletons + block H - 2h = rank H - h", CC, H30 + (H - 2n * H30), H - H30),
    equals(SE, "stage-3 entrance profile 3r + (H - 2r) + (m - 2H - 2r) = m - H - r", CC, 3n * r + (H - 2n * r) + (m - 2n * H - 2n * r), m - H - r),
    fromCheck(SE, { name: "Psi_2(1 - 40315/10^11) < 1 (own enclosures rounded up to 10^-10)", source: CC, lhs: ccb.bound, rel: "<", rhs: ONE }),
    fromCheck(SE, { name: "certified gap > 1.4*10^-12", source: CCR, lhs: st.ccGapDecimal, rel: "<", rhs: ccb.gap }),
    fromCheck(SE, { name: "second route: Psi_2 < 1", source: "derived", lhs: ccb2.bound, rel: "<", rhs: ONE }),
    truth(OBS, "room (controlled corners): largest a_b on the 10^-11 grid (second route)", "derived", true, `${gridCC.k}/10^11`, "observation"),
  );
  const asmCC = batchedAssemblyRows(SE, pcc, { gap: st.ccAgap }, CCR);
  out.push(...asmCC.rows);
  const pct12 = mul(sub(div(pcc.kappa, q(12649n, TEN(11))), ONE), q(100n));
  out.push(
    fromCheck(SE, { name: "1 - sigma <= a_c = 7/10^7 (PR 10's complex network, entry 10)", source: CC, lhs: sub(ONE, pcc.sigma), rel: "<=", rhs: STATED_PR10.ac, kind: "condition" }),
    truth(SE, "59.35% above PR 12's 1.2649e-7", CCR, !lt(pct12, st.ccOverPR12pct[0]) && lt(pct12, st.ccOverPR12pct[1]), toDecimal(pct12, 4) + "%"),
    truth(OBS, "the sub-claim's kappa is below PR 13's 7699/10^10 (the README says so and does not claim it)", CCR, lt(pcc.kappa, q(7699n, TEN(10))), toDecimal(div(q(7699n, TEN(10)), pcc.kappa), 3) + " times smaller", "observation"),
  );

  out.push(
    truth(OBS, "analytic (not checked): the stage-two auxiliary-entrance and data-entrance corner lemmas (Pi_t tensor Pi_U with a nonsingular b-corner of K Pi_U K^{-1}), the stage-three corner I - Z with rank Z <= r and its Schur complement, and the rational witnesses for the new nonzero minors", CC, true, "", "observation"),
    truth(OBS, "analytic (not checked): one controlled basis meets all source-frame exit, join and data conditions at h = 30 (finite product of nonzero polynomials), and the physical pivot order under lower/lower elimination", SFC, true, "", "observation"),
    truth(OBS, "analytic (not checked): the source-frame lemma at h = 30 (PR 13), that the new blocks do not double count the replaced auxiliary edges, and lem:source-corner-chunk-swap", SFC, true, "", "observation"),
    truth(OBS, "not rebuilt here: PR 12's h = 30 producer (c = 16089992); the h = 3, 4, 5 matrix controls of the certificate", SFR, true, "", "observation"),
    ...ANALYTIC_PR10.map((s) => truth(OBS, `analytic, inherited from PR 10 (not checked): ${s}`, "PR10 notes", true, "", "observation")),
  );
  const ordered = [...out.filter((x) => x.section !== OBS), ...out.filter((x) => x.section === OBS)];
  return { results: ordered, values: { params: p, pcc, bit: bn, w, ells, b, b2, complex: cn, cw, c, c2, margins: asm.mg, G: asm.G, cc: { w: ccw, ells: ccE, b: ccb, margins: asmCC.mg, G: asmCC.G }, Rmax, grid: { bit: gridB, cons: gridCons, complex: gridC, ccBit: gridCC } } };
}
