// PR 10 (icekylinx): "Batch recursive networks for a conditional kappa > 2^-23 bound".
// Head 62691e3, base 6e56487 (one commit). It imports PR 7 (and through it PR 3 and
// PR 5) byte-identically: scripts/paired_triple_circuit.py, prime_field_circuit.py,
// complex_circuit.py, fast_gaussian.py, notes/prime-field28-construction.tex,
// notes/complex-circuit-construction.tex and certificates prime-field28.json,
// complex-network.json, fast-gaussian.json have the same blobs as at prs/7.
//
// Top-down: the finite networks of PR 7 are unchanged (bit: h = 28, R = 11840940;
// complex: h = 28, R_c = 93838). Only the cost accounting of the recursion changes:
//  (1) Bit (interchange) network: three large projector classes are compiled with
//      contiguous blocks (projector-batching.tex, batched-bit-rank-accounting.tex),
//      and with a controlled rational basis the stage-two sink becomes two blocks
//      (controlled-projector-basis.tex). The mixed-width moment certifies
//      a_b = 177/10^9 (three classes) and then 246/10^9 (controlled).
//  (2) Complex network: two auxiliary residual classes (ranks m - 2h, m - h^2) are
//      applied as one child each (bulk-complex-guard.tex); the moment certifies
//      a_c = 7/10^7. A new depth guard (rho = 6/5) gives C1 = 6/5 - beta/5 + zeta.
//  (3) Assembly: PR 5's fast-Gaussian system with c = 1, eps = 7999999/16000000,
//      beta = 1/1000, delta = 10^-10, C1 = 11999/10000, lambda = tau + 10^-16,
//      lambda' = tau + 2*10^-16, kappa = 6149999/(5*10^13) > 2^-23.
// The new finite inequalities are the moment bounds, the path moments of the guard
// and the parameter table; everything that turns them into running-time bounds is
// analytic (listed in ANALYTIC_PR10 and printed as observations).

import { q, add, sub, mul, div, lt, le, eq, twoPow, ONE, ZERO, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { layerExponents, type CompactParams } from "../compact/witness";
import { fastParameterChecks, fastMargins, fastMinimumMargin, cutoff64d2, cutoff96d } from "./fastGaussian";
import { primeFieldBitNetwork, primeFieldComplexNetwork, computeComplex7, STATED_PR7 } from "./pr7";
import { momentWeights, momentUpperBound, momentUpperSecond, logInverseEnclosure, largestGridSaving, bitClasses, bulkPathBounds, bulkGuardConstants, slackTable, chirpBudget, type WidthClass } from "./batched";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const RANK = "PR10 batched-bit-rank-accounting.tex";
const CTRL = "PR10 controlled-projector-basis.tex";
const CPLX = "PR10 batched-assembly.tex sec:batched-complex-parameters";
const GUARD = "PR10 bulk-complex-guard.tex";
const ASM = "PR10 batched-assembly.tex / batched-23.patch 08-assembly";
const CHIRP = "PR10 chirp-scaling-correction.tex";
const H = 28n;

export const STATED_PR10 = {
  // bit
  R: 11840940n,
  B: 114371146876896000n,
  ranks: [21896n, 21168n, 21141n],
  singles: [56n, 784n, 811n],
  widths: [21840n, 20384n, 20330n],
  eta: q(39n, 520019360n),
  aMid: q(177n, TEN(9)),
  midLogs: [q(9997n, 1000n), q(512n, 100000n), q(7411n, 100000n), q(768n, 10000n)],
  midGap: q(178n, TEN(12)), // "greater than 1.78 x 10^-10"
  S1: 105555640096680883200n,
  ctrlR: [q(1n, 21952n), q(195n, 196n), q(13n, 14n), q(10165n, 10976n), q(1n, 28n)],
  ctrlW: [q(10841531n, 520019360n), q(12827685n, 26000968n), q(855179n, 1857212n), q(20865n, 2736944n), q(65783n, 3714424n)],
  log28: q(33323n, 10000n),
  a: q(246n, TEN(9)),
  ctrlGap: q(476n, TEN(13)), // "exceeding 4.76 x 10^-11"
  // complex
  vc: 3276n,
  Rc: 93838n,
  auxRoles: 93867n,
  Bc: 1007397164592n,
  Wc: 2085111546336n,
  Lc: 26143580736n,
  sc: 45772350635112192n,
  cRanks: [21896n, 21168n],
  Sc: 2389799139122304n,
  etac: q(5n, 12693352n),
  ac: q(7n, TEN(7)),
  cLogs: [q(9997n, 1000n), q(2555n, TEN(6)), q(36368n, TEN(6))],
  cGap: q(24132873235669673777179671369131n, 1525632551364197359955324563293421369131n),
  cGapDecimal: q(158n, TEN(10)), // "> 1.58 x 10^-8"
  // guard
  qq: 22120n,
  pathBounds: [q(553n, 4000n), q(47817969n, 47897500n), q(1213697n, 1260000n)],
  theta: q(999n, 1000n),
  C1: q(11999n, 10000n),
  oneMinusEpsC1: q(64008011999n, 160000000000n),
  epsC1: q(95991988001n, 160000000000n),
  // assembly
  table: [
    q(499999877n, 500000000n), q(123n, 500000000n), q(9999993n, 10000000n), q(7n, 10000000n), q(1n), q(7999999n, 16000000n), q(1n, 1000n), q(999n, 1000n),
    q(1n, TEN(16)), q(4540000001n, TEN(16)), q(2459999999n, TEN(16)), q(1n, TEN(16)), q(1n, TEN(16)), q(2266500001n, 5n * TEN(15)), q(1229999999n, 5n * TEN(15)),
    q(64008011999n, 160000000000n), q(984000123n, 8n * TEN(15)), q(1n, 8000000n), q(312500039n, 625000000n), q(1n, TEN(10)), q(1249999999n, TEN(10)),
    q(1n, 8000000n), q(1n, 8000000n), q(7999999n, 16000000n), q(8000001n, 16000000n), q(6149999n, 5n * TEN(13)), q(1249n, TEN(10)), q(1n, 8000000n),
    q(4999998770000001n, 5n * TEN(15)),
  ],
  margins: {
    g1: q(1n, 8000000n),
    g2: q(983999877n, 8n * TEN(15)),
    g3: q(9839998762000001n, 8n * TEN(22)),
    g4: q(984000123n, 8n * TEN(15)),
    g5: q(1249n, TEN(10)),
    g6: q(312500039n, 625000000n),
    g7: q(7999999n, 16000000n),
  } as Record<string, Q>,
  gap: q(362000001n, 8n * TEN(22)),
  leafGap: q(6993n, TEN(10)),
  kappaDecimal: "0.00000012299998",
  alphaExp: q(8000001n, 32000000n),
  KExp: q(7999999n, 16000000n),
  ellExp: q(8000001n, 16000000n),
  primeExp: q(1n, 8000000n),
};

export function pr10Params(): CompactParams {
  const a = q(246n, TEN(9));
  const ac = q(7n, TEN(7));
  const tau = sub(ONE, a);
  return {
    a,
    ac,
    tau,
    sigma: sub(ONE, ac),
    epsilon: q(7999999n, 16000000n),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(10)),
    C1: q(11999n, 10000n),
    lambda: add(tau, q(1n, TEN(16))),
    lambdaPrime: add(tau, q(2n, TEN(16))),
    kappa: q(6149999n, 5n * TEN(13)),
  };
}

/** Analytic statements of PR 10 (not finite arithmetic; printed as observations, never counted). */
export const ANALYTIC_PR10 = [
  "the arbitrary-width recurrence lemma: Psi(tau) < 1 implies F(e) = O(e^tau) for the integer-width recurrence with floors, remainders and row padding (batched-bit-rows.tex)",
  "the large-projector factorization: a rational idempotent of rank a > m/2 with an invertible corner has exactly m - a corner pivots and one contiguous identity block of size 2a - m under the rightmost-pivot rule (projector-batching.tex)",
  "existence of one rational basis S meeting all corner conditions simultaneously (nonvanishing-polynomial argument; not materialized at h = 28) and of the controlled basis with a diagonal stage-two corner (controlled-projector-basis.tex)",
  "that the three classes are what the producer's frames give (ranks m - 2h, m - h^2, (h^2-1)(h-1), copies v^2 R, v^2 R, 2v^3) and that dummy padding roles realize them exactly",
  "the whole-residual complex child: C^{-1} = -i Z C Z and the tensor sign identity, orthonormal residual bases in the first a slots (bulk-complex-guard.tex, batched-complex-rows.tex)",
  "the dependency-path budget q = m + 6h (one central return per stage; batched-path-budget.tex) and the depth induction A(e) <= C_dep d^(-beta(rho-1)) e^rho",
  "the mixed-width complex layer bound O((log p)^3 [d^chi + d^(sigma+beta(1-sigma)) + d^max{1-c,0} + 1]) and the compact-control interface at c = 1",
  "the chirp precision correction F = 2^B (only the integer budget is checked here) and the compact sorting cost with exceptional fraction 5/(128 p^3)",
  "completeness of the cost table and the eventual conditions (b >= 64 d^2 holds only for b >= 2^(6/(1-2eps)) = 2^48000000)",
];

export type PR10Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR10> };

/** The rows shared by PRs 10, 12 and 13 for an assembly in the batched system. */
export function batchedAssemblyRows(section: string, p: CompactParams, st: { table?: Q[]; margins?: Record<string, Q>; gap?: Q; leafGap?: Q; C1?: Q; rho?: Q }, src: string) {
  const out: Result[] = [];
  const x = layerExponents(p);
  const mg = fastMargins(p);
  const G = fastMinimumMargin(p);
  out.push(...fastParameterChecks(p).map((k) => fromCheck(section, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(section, { name: `kappa < ${k}`, source: src + " margins (g4 = (1-eps)(1-tau), g5 = 1 - delta - 2 eps)", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(section, "sigma < tau, so chi = tau", src, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    fromCheck(section, { name: "leaf exponent sigma + beta(1 - sigma) < tau", source: src, lhs: x.leaf, rel: "<", rhs: p.tau, kind: "condition" }),
    st.rho === undefined
      ? equals(section, "C1 = 6/5 - beta/5 + zeta (the bulk guard's exponent)", src, add(sub(q(6n, 5n), div(p.beta, q(5n))), p.zeta), p.C1)
      : equals(section, `C1 = rho - (rho - 1) beta + zeta with rho = ${show(st.rho)} (the guard's exponent)`, src, add(sub(st.rho, mul(sub(st.rho, ONE), p.beta)), p.zeta), p.C1),
    equals(section, "G_* = g3", src, G, mg.g3),
  );
  if (st.leafGap) out.push(equals(section, `leaf exponent = 1 - ${show(st.leafGap)}`, src, x.leaf, sub(ONE, st.leafGap)));
  if (st.margins) for (const [k, v] of Object.entries(st.margins)) out.push(equals(section, `margin ${k} as stated`, src, mg[k as keyof typeof mg], v));
  if (st.gap) out.push(equals(section, "G_* - kappa as stated", src, sub(G, p.kappa), st.gap));
  if (st.table) {
    const t = slackTable(p as any, x.chi, x.leaf);
    if (t.length !== st.table.length) throw new Error("table length");
    t.forEach(([name, v], i) => out.push(equals(section, `slack table row ${i + 1}: ${name}`, src + " (twenty-nine strict parameter slacks)", v, st.table![i]!)));
    out.push(truth(section, "all 29 table slacks positive", src, t.every(([, v]) => lt(ZERO, v)), `${t.length} rows`));
  }
  return { rows: out, x, mg, G };
}

export function pr10(opts: PR10Options = {}) {
  const st = { ...STATED_PR10, ...opts.stated };
  const p = opts.p ?? pr10Params();
  const out: Result[] = [];
  const OBS = "PR10-0 observations and analytic steps (not counted)";

  // ---- 10A: bit network counts (PR 7's network, unchanged)
  const SA = "PR10-A bit network: PR 7's counts and the three large projector classes";
  const bn = primeFieldBitNetwork(Number(H), st.R);
  const v = bn.v;
  const m = bn.m;
  const three = bitClasses(H, v, st.R, "three");
  out.push(
    equals(SA, "R is PR 7's role count (rebuilt in entry 7)", RANK, st.R, STATED_PR7.R, "identity"),
    equals(SA, "B = v^2 R", RANK, v * v * st.R, st.B),
    equals(SA, "eta = (Wm - s)/(Wm) (PR 7's deficit)", RANK, bn.eta, st.eta),
    equals(SA, "rank m - 2h of the stage 1-3 join", RANK, three.ranks.a1, st.ranks[0]!),
    equals(SA, "rank m - h^2 of the stage 2 sink", RANK, three.ranks.a2, st.ranks[1]!),
    equals(SA, "rank d_3 = (h^2-1)(h-1) of the stage 3 data entrance", RANK, three.ranks.a3, st.ranks[2]!),
    equals(SA, "singleton pivots m - a_i", RANK, [three.ranks.a1, three.ranks.a2, three.ranks.a3].map((a) => m - a).join(","), st.singles.join(",")),
    equals(SA, "batched widths 2a_i - m", RANK, three.classes.map((c) => c.t).join(","), st.widths.join(",")),
    truth(SA, "every selected rank exceeds m/2 and every block width is in [1, m - 2]", "PR10 projector-batching.tex", [three.ranks.a1, three.ranks.a2, three.ranks.a3].every((a) => 2n * a > m) && three.classes.every((c) => c.t >= 1n && c.t <= m - 2n)),
    equals(SA, "data rank sum: 2N sum_j (d_j + h - 1) + N = 2Nm - N, d_j = (h^(j-1) - 1)(h - 1)", RANK, 2n * bn.N * [1n, H, H * H].reduce((s, a) => s + (a - 1n) * (H - 1n) + H - 1n, 0n) + bn.N, 2n * bn.N * m - bn.N, "identity"),
    truth(SA, "d_3 > m/2 and the other ranks inside an invocation (h, h^2 - h) are below m/2", RANK, 2n * three.ranks.a3 > m && 2n * (H * H - H) < m, "", "constant"),
  );

  // ---- 10B: the intermediate three-class moment (a_b = 177/10^9)
  const SB = "PR10-B three-class mixed-width moment, a_b = 177/10^9 (intermediate)";
  const mid = momentWeights(m, bn.W, bn.s, three.classes);
  out.push(...logBoundRows(SB, mid.items, st.midLogs, RANK));
  const midB = momentUpperBound(mid.items, st.aMid, st.midLogs);
  out.push(
    equals(SB, "sum of rank-mass weights = s/(Wm) = 1 - eta (batching keeps the rank sum)", RANK, mid.total, sub(ONE, bn.eta), "identity"),
    fromCheck(SB, { name: "sum w_i/(1 - a l_i) < 1 at a = 177/10^9", source: RANK, lhs: midB.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "gap > 1.78*10^-10", source: RANK, lhs: st.midGap, rel: "<", rhs: midB.gap }),
  );

  // ---- 10C: the controlled basis moment (a_b = 246/10^9)
  const SC = "PR10-C controlled-basis moment (stage-two sink as blocks H and m - 2H), a_b = 246/10^9";
  const ctrl = bitClasses(H, v, st.R, "controlled");
  const cw = momentWeights(m, bn.W, bn.s, ctrl.classes);
  const ctrlLogs = [...st.midLogs, st.log28];
  out.push(
    equals(SC, "S_1 = S_0 - B H (singleton calls)", CTRL, cw.S, st.S1),
    equals(SC, "S_0 - S_1 = B h^2", CTRL, mid.S - cw.S, st.B * H * H, "identity"),
    equals(SC, "normalized child widths", CTRL, cw.items.map((x) => show(x.r)).join(","), st.ctrlR.map(show).join(",")),
    equals(SC, "rank-mass weights", CTRL, cw.items.map((x) => show(x.w)).join(","), st.ctrlW.map(show).join(",")),
    equals(SC, "weights sum to 1 - eta", CTRL, cw.total, sub(ONE, bn.eta), "identity"),
    ...logBoundRows(SC, cw.items, ctrlLogs, CTRL),
  );
  const cB = momentUpperBound(cw.items, st.a, ctrlLogs);
  const c2 = momentUpperSecond(cw.items, st.a);
  out.push(
    fromCheck(SC, { name: "sum w_i/(1 - a l_i) < 1 at a = 246/10^9", source: CTRL, lhs: cB.bound, rel: "<", rhs: ONE }),
    fromCheck(SC, { name: "gap > 4.76*10^-11", source: CTRL, lhs: st.ctrlGap, rel: "<", rhs: cB.gap }),
    fromCheck(SC, { name: "second route: Psi(1-a) < 1 with this checker's log enclosures and e^x <= 1 + x + x^2/(2(1-x/3))", source: "derived", lhs: c2.bound, rel: "<", rhs: ONE }),
    fromCheck(SC, { name: "1 - tau <= a_b", source: ASM, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
  );
  const gridB = cached("pr10 grid bit", () => largestGridSaving(cw.items, TEN(9), 246n));
  const gridMid = cached("pr10 grid mid", () => largestGridSaving(mid.items, TEN(9), 177n));
  const uniform = cached("pr10 uniform", () => logIntegerEnclosure(m, 24));
  out.push(
    truth(OBS, "room: largest a_b on the 10^-9 grid (second route) for the controlled and the three-class moments", "derived", true, `controlled ${gridB.k}/10^9 (Psi >= 1 from ${gridB.firstFail}/10^9 on); three-class ${gridMid.k}/10^9`, "observation"),
    truth(OBS, "without batching the same network certifies only about 7.5e-9 (PR 7)", "derived", true, `-log(1-eta)/log m ~ ${toDecimal(div(bn.eta, uniform.lower), 12)}; batching multiplies the bit saving by about ${toDecimal(div(st.a, div(bn.eta, uniform.lower)), 2)}`, "observation"),
  );

  // ---- 10D: complex network with whole-residual children
  const SD = "PR10-D complex network (PR 7's, h = 28) with two whole-residual classes, a_c = 7/10^7";
  const cc = computeComplex7();
  const Rc = BigInt(cc.additions + cc.injections);
  const cn = primeFieldComplexNetwork(Number(H), Rc);
  const Bc = cn.v * cn.v * (Rc + H + 1n);
  const cClasses: WidthClass[] = st.cRanks.map((a, i) => ({ name: `whole residual rank ${a}`, copies: Bc, t: a }));
  const cxw = momentWeights(cn.m, cn.W, cn.s, cClasses);
  out.push(
    equals(SD, "v_c = C(28,3)", CPLX, cn.v, st.vc),
    equals(SD, "R_c (PR 7's complex circuit, rebuilt)", CPLX, Rc, st.Rc),
    equals(SD, "auxiliary roles per invocation R_c + h + 1", CPLX, Rc + H + 1n, st.auxRoles),
    equals(SD, "B_c = v_c^2 (R_c + h + 1)", CPLX, Bc, st.Bc),
    equals(SD, "W_c = 2 v_c^2 (v_c + R_c + h + 1)", CPLX, cn.W, st.Wc),
    equals(SD, "L_c = 3 v_c^2 h(h+1)", CPLX, cn.L, st.Lc),
    equals(SD, "s_c = W_c m - 2 v_c^3 + 2 L_c", CPLX, cn.s, st.sc),
    equals(SD, "a_1 = m - 2h, a_2 = m - h^2", CPLX, `${cn.m - 2n * H},${cn.m - H * H}`, st.cRanks.join(",")),
    equals(SD, "S_c = s_c - B_c(a_1 + a_2)", CPLX, cxw.S, st.Sc),
    equals(SD, "Xi(1) = s_c/(W_c m) = 1 - eta_c", CPLX, cxw.total, sub(ONE, st.etac)),
    ...logBoundRows(SD, cxw.items, st.cLogs, CPLX),
  );
  const cxB = momentUpperBound(cxw.items, st.ac, st.cLogs);
  const cx2 = momentUpperSecond(cxw.items, st.ac);
  const gridC = cached("pr10 grid c", () => largestGridSaving(cxw.items, TEN(8), 70n));
  out.push(
    equals(SD, "gap 1 - sum w_i/(1 - a_c l_i) as stated (exact)", CPLX, cxB.gap, st.cGap),
    fromCheck(SD, { name: "gap > 1.58*10^-8", source: CPLX, lhs: st.cGapDecimal, rel: "<", rhs: cxB.gap }),
    fromCheck(SD, { name: "second route: Xi(1-a_c) < 1 (own log enclosures, sharper exponential bound)", source: "derived", lhs: cx2.bound, rel: "<", rhs: ONE }),
    fromCheck(SD, { name: "1 - sigma <= a_c", source: ASM, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    truth(OBS, "room: largest a_c on the 10^-8 grid (second route)", "derived", true, `${gridC.k}/10^8`, "observation"),
  );

  // ---- 10E: the bulk complex guard
  const SE = "PR10-E depth guard for unequal complex children (rho = 6/5, theta = 999/1000)";
  out.push(...guardRows(SE, cn.m, H, st.cRanks, st.pathBounds, cn.W, cn.s, p, GUARD, st));

  // ---- 10F: assembly
  const SF = "PR10-F assembly: fast-Gaussian system with c = 1, eps = 7999999/16000000, kappa = 6149999/(5*10^13)";
  const asm = batchedAssemblyRows(SF, p, st, ASM);
  out.push(...asm.rows);
  out.push(
    equals(SF, "1 - eps C1", ASM, sub(ONE, mul(p.epsilon, p.C1)), st.oneMinusEpsC1),
    equals(SF, "eps C1", ASM, mul(p.epsilon, p.C1), st.epsC1),
    equals(SF, "alpha exponent (1 - eps)/2", ASM, div(sub(ONE, p.epsilon), q(2n)), st.alphaExp),
    equals(SF, "K exponent eps c", ASM, mul(p.epsilon, p.c), st.KExp),
    equals(SF, "ell exponent 1 - eps", ASM, sub(ONE, p.epsilon), st.ellExp),
    equals(SF, "prime-interval ratio and b/d^2 grow as p^(1 - 2 eps)", ASM, sub(ONE, mul(q(2n), p.epsilon)), st.primeExp),
    fromCheck(SF, { name: "kappa > 2^-23", source: ASM, lhs: twoPow(-23), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SF, { name: "kappa < 2^-22", source: "derived (the dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-22), kind: "condition" }),
    truth(SF, "kappa = 1.2299998e-7 (decimal as stated)", ASM, toDecimal(p.kappa, 14) === st.kappaDecimal, toDecimal(p.kappa, 16)),
    fromCheck(SF, { name: "kappa < g3 = eps(1 - lambda') < a_b/2 (the next ceiling)", source: "derived", lhs: asm.mg.g3, rel: "<", rhs: div(st.a, q(2n)), kind: "implied" }),
  );
  const chirp = cached("chirp budget", () => chirpBudget(3000));
  out.push(truth(SF, "chirp correction: p + 29p + ceil(log2(2^B L_A)) + 11 <= 32.14p + 11 <= 34p for every p = 101..3000 and every 2 <= alpha < sqrt p", CHIRP, chirp.ok, chirp.detail));
  out.push(
    truth(OBS, "kappa / (a_b/2)", "derived", true, toDecimal(div(p.kappa, div(st.a, q(2n))), 7), "observation"),
    truth(OBS, "kappa / 373*10^-11 (PR 7) and / 83*10^-12 (head)", "derived", true, `${toDecimal(div(p.kappa, q(373n, TEN(11))), 3)} and ${toDecimal(div(p.kappa, q(83n, TEN(12))), 1)}`, "observation"),
    truth(OBS, "eventual cutoffs at this eps: b >= 64 d^2 needs b >= 2^(6/(1-2eps)); b >= 96d needs b >= 2^(7/(1-eps))", "derived", true, `2^${toDecimal(cutoff64d2(p.epsilon), 1)} and 2^${toDecimal(cutoff96d(p.epsilon), 4)}`, "observation"),
    ...ANALYTIC_PR10.map((s) => truth(OBS, `analytic (not checked): ${s}`, "PR10 notes", true, "", "observation")),
  );

  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { params: p, bit: bn, mid, midB, ctrl: cw, ctrlB: cB, ctrl2: c2, complex: cn, Rc, Bc, cx: cxw, cxB, cx2, guard: bulkGuardConstants(cn.W, cn.m, p.beta, p.zeta), margins: asm.mg, G: asm.G, grid: { bit: gridB, mid: gridMid, complex: gridC } } };
}

/** Rows: each stated l_i is above this checker's upper enclosure of log(1/r_i). */
export function logBoundRows(section: string, items: { name: string; r: Q }[], ells: Q[], src: string): Result[] {
  return items.map((it, i) => {
    const e = logInverseEnclosure(it.r);
    return fromCheck(section, { name: `log(1/r) < ${show(ells[i]!)} for r = ${show(it.r)} (${it.name})`, source: src + " (positive logarithm series)", lhs: e.upper, rel: "<", rhs: ells[i]! });
  });
}

/** The bulk guard rows (path moments, constants, C1, eps C1 < 1). */
export function guardRows(section: string, m: bigint, h: bigint, ranks: bigint[], stated: Q[], W: bigint, s: bigint, p: CompactParams, src: string, st: { qq?: bigint; theta?: Q }) {
  const out: Result[] = [];
  const g = bulkPathBounds(m, h, ranks);
  const k = bulkGuardConstants(W, m, p.beta, p.zeta);
  const theta = st.theta ?? q(999n, 1000n);
  if (st.qq !== undefined) out.push(equals(section, "path budget q = m + 6h", src, g.qq, st.qq));
  out.push(
    truth(section, "160000^5 < m^6, so m^(6/5) > 160000", src, g.lowerOk),
    truth(section, "every selected rank exceeds q/2 and any two exceed q (at most one selected edge per path)", src, g.atMostOne),
    equals(section, "q/160000 bound", src, g.first, stated[0]!),
    fromCheck(section, { name: "q/m^rho < 999/1000", source: src, lhs: g.first, rel: "<", rhs: theta }),
  );
  g.rows.forEach((r, i) => {
    out.push(
      equals(section, `(q - a)/160000 + Taylor bound of (a/m)^(6/5), a = ${r.a}`, src, r.bound, stated[i + 1]!),
      truth(section, `Taylor value bounds (a/m)^(6/5) from above, a = ${r.a} (exact: (a/m)^6 <= T^5)`, src + " (1-t)^(6/5) <= 1 - 6t/5 + 3t^2/(25(1-t))", r.taylorValid),
      fromCheck(section, { name: `path moment bound < 999/1000, a = ${r.a}`, source: src, lhs: r.bound, rel: "<", rhs: theta }),
    );
  });
  out.push(
    fromCheck(section, { name: "36W^3 + 4s + 4W + 8m + 4 < E = 64(W + m + 1)^3 (complex W, s)", source: src, lhs: q(36n * W ** 3n + 4n * s + 4n * W + 8n * m + 4n), rel: "<", rhs: q(k.E) }),
    truth(section, "leaf: 8 (2m)^(1/5) <= 16m, i.e. 8^5 (2m) <= (16m)^5", src, 8n ** 5n * 2n * m <= (16n * m) ** 5n, "", "constant"),
    truth(section, "induction gap: (1 - 999/1000) C_dep >= E with C_dep = 1000(E + 16m + 1)", src, k.Cdep >= 1000n * k.E, "", "identity"),
    equals(section, "C1 = rho - (rho - 1) beta + zeta", src, k.C1, p.C1),
    fromCheck(section, { name: "eps C1 < 1 (coefficient width O(p))", source: src, lhs: mul(p.epsilon, p.C1), rel: "<", rhs: ONE }),
    truth(section, "C0 = ceil(128 m (1 + 1/zeta) C_dep)", src, k.C0 > 0n, `C0 = ${k.C0}`, "identity"),
  );
  return out;
}
