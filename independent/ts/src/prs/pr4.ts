// PR 4 (David Leen): "Retained complex totals with compact controls".
// Sources: notes/retained-complex-note.tex and notes/retained-complex-construction.tex
// at prs/4 (base 6e56487).
//
// Top-down: a new complex motif at h = 24 (m = 13824). Its side correction is a
// rectangle partition of the disjoint (source, target) triple pairs plus
// fixed-pair trees, and the central coefficient comes from h retained totals
// (pair roots, doubled point totals, the global total) instead of central wires.
// Counts: C = 132180 additions, q = 233580 outputs, R_aux = 365760 roles; with
// shared stage-1/stage-3 banks W = 2N + 2v^2 R_aux, L_loss = 3v^2((h-1)^2 + h),
// s = Wm - 2N + 2 L_loss, eta = 365/5084246016, certifying 1 - sigma = 750/10^11.
// The compact-control system is re-solved with c = 1, lambda = 1 - 2959/10^12,
// lambda' = 1 - 2958/10^12, kappa = 591/10^12 (G_* = g3).

import { q, sub, mul, div, lt, eq, twoPow, ONE, show, toDecimal } from "../rational";
import { ground } from "../networks";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { compactParameterChecks, compactMargins, compactMinimumMargin, layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { gaussianChecks, gaussianInstance } from "../gaussian";
import { BIT_SAVING } from "../checks";
import { binom } from "../intmath";
import { bestPlan, disjointBranch, pairTree, roles } from "./retained";
import { largestGridSaving } from "../ceiling";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const CON = "PR4 retained-complex-construction.tex";
const NOTE = "PR4 retained-complex-note.tex";
const H = 24;

export const STATED_PR4 = {
  v: 2024n,
  m: 13824n,
  disjointRoles: 329811,
  disjointAdditions: 123855,
  disjointOutputs: 205956,
  q2: 27600,
  preRectangleAdditions: 8325,
  C: 132180,
  q: 233580,
  Raux: 365760n,
  ell: 553n,
  W: 3013310215168n,
  Lloss: 6796219584n,
  s: 41655997423981952n,
  eta: q(365n, 5084246016n),
  L0: q(477n, 50n),
  ac: q(750n, TEN(11)),
  deficitSlack: q(11935523n, 49650840000000000n),
  gates: 6696869422848n,
  G: q(2956521n, 5n * TEN(15)),
  gap: q(1521n, 5n * TEN(15)),
};

export function pr4Params(): CompactParams {
  const a = BIT_SAVING;
  const ac = q(750n, TEN(11));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(1999n, 10000n),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(49961n, 10000n),
    lambda: sub(ONE, q(2959n, TEN(12))),
    lambdaPrime: sub(ONE, q(2958n, TEN(12))),
    kappa: q(591n, TEN(12)),
  };
}

/** The counts of "Exact counts and recurrence", from the recomputed parts. */
export function retainedCounts(h: number, disjoint: { additions: number; outputs: number }, pairOutputs: number, pairAdditions: number) {
  const { v, N, m } = ground(h);
  const H_ = BigInt(h);
  const pairsCount = binom(H_, 2n);
  const globalTree = v - 1n; // any binary tree on v leaves
  const pairTrees = pairsCount * BigInt(pairAdditions);
  const pointTrees = (H_ - 1n) * (H_ - 2n); // h-1 trees on h-1 pair roots
  const pre = globalTree + pairTrees + pointTrees;
  const C = pre + BigInt(disjoint.additions);
  const q2 = pairsCount * BigInt(pairOutputs);
  const qq = BigInt(disjoint.outputs) + q2 + H_;
  const Raux = C + qq;
  const ell = (H_ - 1n) ** 2n + H_;
  const W = 2n * N + 2n * v * v * Raux;
  const L = 3n * v * v * ell;
  const s = W * m - 2n * N + 2n * L;
  return { v, N, m, pre, C, q2, q: qq, Raux, ell, W, L, s, deficit: W * m - s, eta: q(W * m - s, W * m) };
}

export function computeRetained() {
  return cached("pr4 retained", () => {
    const plan = bestPlan(H, 3, 3, "first");
    const planLast = bestPlan(H, 3, 3, "last");
    const disjoint = disjointBranch(H, plan);
    return { plan, planLastRoles: roles(planLast), disjoint, tree: pairTree(H - 2, "floor"), treeCeil: pairTree(H - 2, "ceil"), pointTree: pairTree(H - 1, "floor") };
  });
}

export type PR4Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR4>; retained?: ReturnType<typeof computeRetained> };

export function pr4(opts: PR4Options = {}) {
  const st = { ...STATED_PR4, ...opts.stated };
  const p = opts.p ?? pr4Params();
  const out: Result[] = [];
  const R = opts.retained ?? computeRetained();
  const d = R.disjoint;

  // ---- 4A: producer counts
  const SA = "PR4-A retained-total producer at h = 24: counts (recomputed from the note)";
  const nw = retainedCounts(H, d, R.tree.outputs, R.tree.additions);
  out.push(
    equals(SA, "v = C(24,3)", CON, nw.v, st.v),
    equals(SA, "m = 24^3", CON, nw.m, st.m),
    equals(SA, "rectangle plan (row/column/split family, cheapest, first candidate on ties): roles", CON, roles(R.plan), BigInt(st.disjointRoles)),
    truth(SA, "the rectangles partition the disjoint (source, target) pairs exactly", CON + ": an exact partition, not a cover", d.exactPartition, `${d.pairsCovered} pairs`),
    equals(SA, "disjoint pairs = v C(21,3)", CON, BigInt(d.pairsCovered), nw.v * binom(21, 3), "identity"),
    truth(SA, "every frame-bad rectangle (source union = complement of a target) has one target", CON + ": Every repaired rectangle [...] has one target", d.badRectangles === d.badWithOneTarget, `${d.badRectangles} bad rectangles`),
    equals(SA, "repaired disjoint branch: roles (unchanged by the repair)", CON, d.roles, st.disjointRoles),
    equals(SA, "repaired disjoint branch: additions", CON, d.additions, st.disjointAdditions),
    equals(SA, "repaired disjoint branch: outputs q_0", CON, d.outputs, st.disjointOutputs),
    equals(SA, "fixed-pair tree outputs per pair (sum of leaf depths, floor split)", CON + ": q_P", R.tree.outputs, R.tree.formula, "identity"),
    equals(SA, "q_2 = C(24,2) q_P, q_P = n(n-1) - sum_internal (n - |K|), n = 22", CON, Number(nw.q2), st.q2),
    equals(SA, "q_P is the same with the ceil split", CON, R.treeCeil.outputs, R.tree.outputs, "identity"),
    truth(SA, "every selected subtree leaves a spare point beyond r", CON + ": proper variable sets leave a spare point", R.tree.spare && R.treeCeil.spare),
    equals(SA, "additions before rectangles = (v - 1) + C(h,2)(h-3) + (h-1)(h-2)", CON, Number(nw.pre), st.preRectangleAdditions),
    equals(SA, "C = 8325 + rectangle additions", CON, Number(nw.C), st.C),
    equals(SA, "q = q_0 + q_2 + h", CON, Number(nw.q), st.q),
    equals(SA, "R_aux = C + q (the compiler identity applied to the recomputed counts)", CON, nw.Raux, st.Raux, "identity"),
    equals(SA, "ell = (h-1)^2 + h", CON, nw.ell, st.ell, "identity"),
    truth(
      "PR4-0 observations (not part of the claim)",
      "the root role count depends on the tie rule: last minimal candidate kept on ties",
      CON + ": the note does not fix ties or split points",
      true,
      `roles ${R.planLastRoles} (first: ${roles(R.plan)}); with that plan the largest 10^-11 grid saving is ${largestGridSaving(retainedCounts(H, { additions: 0, outputs: Number(R.planLastRoles) }, R.tree.outputs, R.tree.additions).eta, st.L0, TEN(11))}`,
      "observation",
    ),
    truth("PR4-0 observations (not part of the claim)", "rectangles that repeat an earlier source family (could share one source tree)", CON, true, `${d.duplicateSourceFamilies} of ${d.repairedRectangles} rectangles; ${d.duplicateAdditions} additions`, "observation"),
  );

  // ---- 4B: network counts and the complex saving
  const SB = "PR4-B network counts, eta, 1 - sigma = 750/10^11";
  const logm = cached("pr4 logm", () => logIntegerEnclosure(nw.m, 24));
  const expL0 = cached(`pr4 exp ${show(st.L0)}`, () => expLowerBound(st.L0, 60));
  const enc = savingEnclosure(nw.eta, logm);
  out.push(
    equals(SB, "W = 2N + 2v^2 R_aux", CON, nw.W, st.W),
    equals(SB, "L_loss = 3 v^2 ell", CON, nw.L, st.Lloss),
    equals(SB, "s = Wm - 2N + 2 L_loss", CON, nw.s, st.s),
    equals(SB, "eta = (Wm - s)/(Wm)", CON, nw.eta, st.eta),
    truth(SB, "L_loss < N (positive deficit)", CON, nw.L < nw.N),
    fromCheck(SB, { name: "log m < 477/50 (atanh, 24 terms)", source: CON, lhs: logm.upper, rel: "<", rhs: st.L0 }),
    truth(SB, "e^(477/50) > m (Taylor partial sum, second route)", CON, lt(q(nw.m), expL0)),
    equals(SB, "eta - (750/10^11)(477/50) = 11935523/49650840000000000", CON, sub(nw.eta, mul(st.ac, st.L0)), st.deficitSlack),
    fromCheck(SB, { name: "eta > a_c (477/50), a_c = 750/10^11", source: CON, lhs: mul(st.ac, st.L0), rel: "<", rhs: nw.eta, kind: "implied" }),
    truth(SB, "a_c < lower enclosure of the actual saving -log(1 - eta)/log m (Mercator route)", CON, lt(st.ac, enc.lower), `a* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    fromCheck(SB, { name: "stated gate count 6696869422848 < 12 W", source: CON, lhs: q(st.gates), rel: "<", rhs: q(12n * nw.W) }),
    truth(
      "PR4-0 observations (not part of the claim)",
      "stated gate count = 3v^2 (4(v + C) + 4v + 4) (PR 3's per-invocation formula; PR 4 states only the total)",
      CON,
      st.gates === 3n * nw.v * nw.v * (4n * (nw.v + nw.C) + 4n * nw.v + 4n),
      "",
      "observation",
    ),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: CON, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "1 - tau <= a_b = 296/10^11 (bit network unchanged; B2 of `bun run check`)", source: CON, lhs: sub(ONE, p.tau), rel: "<=", rhs: BIT_SAVING, kind: "condition" }),
  );

  // ---- 4C: generalized guard
  const SC = "PR4-C generalized guard with the h = 24 network (beta = 1/1000, zeta = 1/10000)";
  const gu = compactGuardConstants(nw.W, nw.s, nw.m, p.zeta);
  out.push(...compactGuardChecks(nw.W, nw.s, nw.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SC, k)));
  out.push(
    fromCheck(SC, {
      name: "36W^3 + 4s + 4W + 4 < E (inverse-child corrections; implied by E = 64(W+m+1)^3)",
      source: CON,
      lhs: q(36n * nw.W ** 3n + 4n * nw.s + 4n * nw.W + 4n),
      rel: "<",
      rhs: q(gu.E),
      kind: "implied",
    }),
  );
  const depth = cached(`pr4 depth ${show(p.beta)}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], nw.m, nw.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SC, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));

  // ---- 4D: parameters and margins
  const SD = "PR4-D compact-control parameters, layer exponents, margins";
  const x = layerExponents(p);
  const mg = compactMargins(p);
  const G = compactMinimumMargin(p);
  out.push(...compactParameterChecks(p).map((k) => fromCheck(SD, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SD, { name: `kappa < ${k}`, source: CON + ": all seven assembly margins are strict", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SD, "sigma < tau, so chi = tau", CON, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SD, "chi_reserve = max{1 - c, 0} = 0 at c = 1", CON, x.reserve, q(0n)),
    equals(SD, "G_* = g3", CON, G, mg.g3),
    equals(SD, "G_* = 2956521/(5*10^15)", CON, G, st.G),
    equals(SD, "G_* - kappa = 1521/(5*10^15)", CON, sub(G, p.kappa), st.gap),
    fromCheck(SD, { name: "kappa > 2^-31", source: CON, lhs: twoPow(-31), rel: "<", rhs: p.kappa, kind: "condition" }),
    equals(SD, "kappa / (83/10^12) = 591/83", CON, div(p.kappa, q(83n, TEN(12))), q(591n, 83n)),
  );

  // ---- 4E: Gaussian width (eps unchanged at 1999/10000)
  const SE = "PR4-E Gaussian width (eps = 1999/10000, unchanged)";
  out.push(...gaussianChecks(p.epsilon, q(15997n, 20000n), "compact-control-34.patch eq:gamma (retained)", 46n).map((k) => fromCheck(SE, k)));
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`gauss ${e} ${show(p.epsilon)}`, () => gaussianInstance(e, p.epsilon));
    out.push(truth(SE, `b = 2^${e}: alpha, gamma meet every stated bound`, "retained", r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }

  // ---- 4F: the same scoped ceiling as PR 3 (not stated by PR 4; an implied comparison)
  const SF = "PR4-F bit-limited ceiling kappa < a/5 (not stated by PR 4)";
  out.push(fromCheck(SF, { name: "kappa < g3 = eps(1 - lambda') < eps a < a/5", source: "implied by tau < lambda < lambda' and g5 > 0", lhs: mg.g3, rel: "<", rhs: div(p.a, q(5n)), kind: "implied" }));

  // observations last, in one section
  const OBS = "PR4-0 observations (not part of the claim)";
  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { network: nw, retained: R, logm, enclosure: enc, guard: gu, params: p, exponents: x, margins: mg, G } };
}


