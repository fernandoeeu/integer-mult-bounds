// PR 13 (eumemic): "auxiliary source frames for kappa 7699/10^10". Head 3ef246f on top
// of PR 10's commit 62691e3 (so it contains PR 10, and through it PR 7, byte-identically).
// Sources: notes/source-frame-bit.tex, source-frame-complex.tex, source-frame-assembly.tex,
// source-frame-21-note.tex, docs/research/source-frames.md.
//
// Top-down: the finite networks are PR 7's, the batching interface is PR 10's.
//  (1) Bit: an auxiliary role may start in any fixed frame M and end in I + M (the
//      transfer needs only sink - source = I). Starting every stage-two auxiliary role
//      at P_{D_0} makes its entrance edge rank 0 (was h^2 - h singletons) and its exit
//      rank m - h (h singleton pivots and one block of m - 2h), replacing PR 10's sink
//      (H corner block + m - 2H block). Rank sum unchanged; the moment certifies
//      a_b = 154/10^8 (PR 10: 246/10^9).
//  (2) Complex: the stage-three data entrances (rank (h^2-1)(h-1), 2 v_c^3 copies) become
//      a third whole-residual class; a_c = 18/10^7. The guard keeps rho = 6/5 with a
//      third path moment.
//  (3) Assembly: PR 10's system with eps = 499999/10^6, kappa = 7699/10^10 > 2^-21.

import { q, add, sub, mul, div, lt, twoPow, ONE, show, toDecimal, type Q } from "../rational";
import { type CompactParams } from "../compact/witness";
import { cutoff64d2 } from "./fastGaussian";
import { primeFieldBitNetwork, primeFieldComplexNetwork, computeComplex7, STATED_PR7 } from "./pr7";
import { momentWeights, momentUpperBound, momentUpperSecond, largestGridSaving, bitClasses, type WidthClass } from "./batched";
import { batchedAssemblyRows, logBoundRows, guardRows, STATED_PR10, ANALYTIC_PR10 } from "./pr10";
import { equals, truth, fromCheck, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const BIT = "PR13 source-frame-bit.tex";
const CPX = "PR13 source-frame-complex.tex";
const ASM = "PR13 source-frame-assembly.tex";
const H = 28n;

export const STATED_PR13 = {
  R: 11840940n,
  B: 114371146876896000n,
  ranks: [21896n, 21141n, 21924n],
  singles: [56n, 811n, 28n],
  widths: [21840n, 20330n, 21896n],
  Sprime: 22293445170300595200n,
  r: [q(1n, 21952n), q(195n, 196n), q(10165n, 10976n), q(391n, 392n)],
  w: [q(2289741n, 520019360n), q(12827685n, 26000968n), q(20865n, 2736944n), q(25721153n, 52001936n)],
  logs: [q(9997n, 1000n), q(512n, TEN(5)), q(768n, TEN(4)), q(2555n, TEN(6))],
  a: q(154n, TEN(8)),
  gap: q(9704597579224556535778749633448639054699n, 20663392005574270637817582110595278287793980851574n),
  gapDecimal: q(469n, TEN(12)),
  // complex
  d3: 21141n,
  d3copies: 70317217152n,
  Sc: 903222851311872n,
  cr: [q(1n, 21952n), q(391n, 392n), q(27n, 28n), q(21141n, 21952n)],
  cw: [q(250477n, 12693352n), q(12233999n, 25386704n), q(844803n, 1813336n), q(824499n, 25386704n)],
  cLogs: [q(9997n, 1000n), q(2555n, TEN(6)), q(36368n, TEN(6)), q(37644n, TEN(6))],
  ac: q(18n, TEN(7)),
  cGap: q(12084702927461727916508294311187513281917509n, 3098906698934144550424761963671962638378246719417509n),
  cGapDecimal: q(389n, TEN(11)),
  pathBounds: [q(553n, 4000n), q(47817969n, 47897500n), q(1213697n, 1260000n), q(372026142559n, 386739360000n)],
  // assembly
  leafGap: q(17982n, TEN(10)),
  oneMinusEpsC1: q(4000511999n, TEN(10)),
  margins: {
    g1: q(1n, 500000n),
    g2: q(38499923n, 5n * TEN(13)),
    g3: q(3849992299500001n, 5n * TEN(21)),
    g4: q(38500077n, 5n * TEN(13)),
    g5: q(19999n, TEN(10)),
    g6: q(5000009999n, TEN(10)),
    g7: q(499999n, TEN(6)),
  } as Record<string, Q>,
  agap: q(492299500001n, 5n * TEN(21)),
};

export function pr13Params(): CompactParams {
  const a = q(154n, TEN(8));
  const ac = q(18n, TEN(7));
  const tau = sub(ONE, a);
  return {
    a,
    ac,
    tau,
    sigma: sub(ONE, ac),
    epsilon: q(499999n, TEN(6)),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(10)),
    C1: q(11999n, 10000n),
    lambda: add(tau, q(1n, TEN(16))),
    lambdaPrime: add(tau, q(2n, TEN(16))),
    kappa: q(7699n, TEN(10)),
  };
}

export function pr13(opts: { p?: CompactParams; stated?: Partial<typeof STATED_PR13> } = {}) {
  const st = { ...STATED_PR13, ...opts.stated };
  const p = opts.p ?? pr13Params();
  const out: Result[] = [];
  const OBS = "PR13-0 observations and analytic steps (not counted)";

  // ---- 13A: the source-frame exit and the new bit moment
  const SA = "PR13-A bit network with auxiliary source frames (stage-two exit of rank m - h), a_b = 154/10^8";
  const bn = primeFieldBitNetwork(Number(H), st.R);
  const m = bn.m;
  const sf = bitClasses(H, bn.v, st.R, "sourceFrames");
  const ctrl = bitClasses(H, bn.v, st.R, "controlled");
  const w = momentWeights(m, bn.W, bn.s, sf.classes);
  const w10 = momentWeights(m, bn.W, bn.s, ctrl.classes);
  const r = sf.ranks as { a1: bigint; a2: bigint; a3: bigint; a4: bigint };
  out.push(
    equals(SA, "R is PR 7's role count (rebuilt in entry 7)", BIT, st.R, STATED_PR7.R, "identity"),
    equals(SA, "B = v^2 R", BIT, bn.v * bn.v * st.R, st.B),
    equals(SA, "ranks: join m - 2h, data entrance (h^2-1)(h-1), exit m - h", BIT, `${r.a1},${r.a3},${r.a4}`, st.ranks.join(",")),
    equals(SA, "singleton pivots m - a", BIT, `${m - r.a1},${m - r.a3},${m - r.a4}`, st.singles.join(",")),
    equals(SA, "block widths 2a - m", BIT, sf.classes.map((c) => c.t).join(","), st.widths.join(",")),
    equals(SA, "per stage-two role: entrance h^2 - h + climb h + sink m - h^2 = 0 + h + (m - h) = m (rank per role unchanged)", BIT, H * H - H + H + (m - H * H), 0n + H + (m - H), "identity"),
    equals(SA, "S' = s - sum copies x widths", BIT, w.S, st.Sprime),
    equals(SA, "S' = S_1 - B(h^2 - 2h), with PR 10's controlled S_1 = 105555640096680883200", BIT, w10.S - st.B * (H * H - 2n * H), st.Sprime),
    equals(SA, "PR 10's S_1 (same formula, controlled classes)", BIT, w10.S, STATED_PR10.S1, "identity"),
    equals(SA, "normalized child widths", BIT, w.items.map((x) => show(x.r)).join(","), st.r.map(show).join(",")),
    equals(SA, "rank-mass weights", BIT, w.items.map((x) => show(x.w)).join(","), st.w.map(show).join(",")),
    equals(SA, "weights sum to 1 - eta, eta = 39/520019360", BIT, w.total, sub(ONE, q(39n, 520019360n))),
    ...logBoundRows(SA, w.items, st.logs, BIT),
  );
  const b = momentUpperBound(w.items, st.a, st.logs);
  const b2 = momentUpperSecond(w.items, st.a);
  const gridB = cached("pr13 grid bit", () => largestGridSaving(w.items, TEN(8), 154n));
  out.push(
    equals(SA, "gap 1 - sum w_i/(1 - a l_i) as stated (exact)", BIT, b.gap, st.gap),
    fromCheck(SA, { name: "gap > 4.69*10^-10", source: BIT, lhs: st.gapDecimal, rel: "<", rhs: b.gap }),
    fromCheck(SA, { name: "second route: Psi(1-a_b) < 1 (own log enclosures, sharper exponential bound)", source: "derived", lhs: b2.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "1 - tau <= a_b", source: ASM, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    truth(OBS, "room: largest a_b on the 10^-8 grid (second route)", "derived", true, `${gridB.k}/10^8 (Psi >= 1 from ${gridB.firstFail}/10^8)`, "observation"),
  );

  // ---- 13B: complex network with a third whole-residual class
  const SB = "PR13-B complex network with three whole-residual classes, a_c = 18/10^7";
  const cc = computeComplex7();
  const Rc = BigInt(cc.additions + cc.injections);
  const cn = primeFieldComplexNetwork(Number(H), Rc);
  const Bc = cn.v * cn.v * (Rc + H + 1n);
  const d3 = (H * H - 1n) * (H - 1n);
  const classes: WidthClass[] = [
    { name: "whole residual rank m - 2h", copies: Bc, t: cn.m - 2n * H },
    { name: "whole residual rank m - h^2", copies: Bc, t: cn.m - H * H },
    { name: "stage-three data entrance", copies: 2n * cn.v ** 3n, t: d3 },
  ];
  const cw = momentWeights(cn.m, cn.W, cn.s, classes);
  out.push(
    equals(SB, "d_3 = (h^2 - 1)(h - 1)", CPX, d3, st.d3),
    equals(SB, "2 v_c^3 data entrance edges", CPX, 2n * cn.v ** 3n, st.d3copies),
    equals(SB, "B_c (PR 10)", CPX, Bc, STATED_PR10.Bc),
    equals(SB, "S_c' = s_c - B_c(a_1 + a_2) - 2 v_c^3 d_3", CPX, cw.S, st.Sc),
    equals(SB, "normalized child widths", CPX, cw.items.map((x) => show(x.r)).join(","), st.cr.map(show).join(",")),
    equals(SB, "rank-mass weights", CPX, cw.items.map((x) => show(x.w)).join(","), st.cw.map(show).join(",")),
    equals(SB, "weights sum to 1 - eta_c", CPX, cw.total, sub(ONE, q(5n, 12693352n))),
    ...logBoundRows(SB, cw.items, st.cLogs, CPX),
  );
  const c = momentUpperBound(cw.items, st.ac, st.cLogs);
  const c2 = momentUpperSecond(cw.items, st.ac);
  const gridC = cached("pr13 grid c", () => largestGridSaving(cw.items, TEN(8), 180n));
  out.push(
    equals(SB, "gap as stated (exact)", CPX, c.gap, st.cGap),
    fromCheck(SB, { name: "gap > 3.89*10^-9", source: CPX, lhs: st.cGapDecimal, rel: "<", rhs: c.gap }),
    fromCheck(SB, { name: "second route: Xi(1-a_c) < 1", source: "derived", lhs: c2.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: ASM, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "a_c > a_b (sigma < tau: the complex network does not bind)", source: CPX, lhs: st.a, rel: "<", rhs: st.ac }),
    truth(OBS, "room: largest a_c on the 10^-8 grid (second route)", "derived", true, `${gridC.k}/10^8`, "observation"),
  );

  // ---- 13C: guard with three classes
  const SC = "PR13-C depth guard with three selected complex classes";
  out.push(...guardRows(SC, cn.m, H, [cn.m - 2n * H, cn.m - H * H, d3], st.pathBounds, cn.W, cn.s, p, CPX, { qq: 22120n }));
  out.push(equals(SC, "(q - d_3) = 979, so (q - d_3)/160000 = 979/160000", CPX, q(22120n - d3, 160000n), q(979n, 160000n), "identity"));

  // ---- 13D: assembly
  const SD = "PR13-D assembly: PR 10's system with eps = 499999/10^6, kappa = 7699/10^10";
  const asm = batchedAssemblyRows(SD, p, { margins: st.margins, gap: st.agap, leafGap: st.leafGap }, ASM);
  out.push(...asm.rows);
  out.push(
    equals(SD, "1 - eps C1", ASM, sub(ONE, mul(p.epsilon, p.C1)), st.oneMinusEpsC1),
    equals(SD, "1 - 2 eps = 1/500000", ASM, sub(ONE, mul(q(2n), p.epsilon)), q(1n, 500000n)),
    fromCheck(SD, { name: "kappa > 2^-21", source: ASM, lhs: twoPow(-21), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < 2^-20", source: "derived (the dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-20), kind: "condition" }),
    truth(OBS, "kappa / (a_b/2), kappa / PR 10's kappa", "derived", true, `${toDecimal(div(p.kappa, div(st.a, q(2n))), 7)}; ${toDecimal(div(p.kappa, STATED_PR10.table[25]!), 4)}`, "observation"),
    truth(OBS, "b >= 64 d^2 eventually needs b >= 2^(6/(1-2eps))", "derived", true, `2^${toDecimal(cutoff64d2(p.epsilon), 1)}`, "observation"),
    truth(OBS, "analytic (not checked): the auxiliary source-frame lemma (Phi_{I+M} Phi_{-M} = Phi_I and that gates and interior edges are unchanged), the common basis for the new exit class (lem:source-frame-basis), and the exit being the idempotent P onto D_0 perp D_1^perp of rank m - h", "PR13 notes", true, "", "observation"),
    ...ANALYTIC_PR10.map((s) => truth(OBS, `analytic, inherited from PR 10 (not checked): ${s}`, "PR10 notes", true, "", "observation")),
  );

  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { params: p, bit: bn, sf: w, b, b2, complex: cn, cw, c, c2, margins: asm.mg, G: asm.G, grid: { bit: gridB, complex: gridC } } };
}
