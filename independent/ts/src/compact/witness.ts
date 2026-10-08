// The parameter system behind the compact-control witness kappa = 83/10^12.
//
// Sources (re-typed from the TeX, not from the Python):
//  - notes/compact-control-note.tex, section "Parameters and complete assembly":
//    the parameter values, the layer exponents chi, chi_leaf, chi_reserve, the
//    displayed comparisons, the seven margins, G_* = g3 and G_* - kappa.
//  - notes/compact-control-layout.tex, "Unrolling the compact-control recurrence":
//    the layer conditions max{tau,sigma,chi} < lambda < lambda' < 1 and
//    max{sigma + beta(1-sigma), 1-c, 0} < lambda'.
//  - notes/compact-control-guard.tex: C1 = 5 - 4 beta + zeta, rational 0 < beta < 1, zeta > 0.
//  - patches/compact-control-34.patch, 05-layers prop:simultaneous-layer (patched):
//    "fixed positive rational numbers c, eps, lambda, lambda', beta, zeta with
//    0 < beta < 1", the two displayed conditions and eps C1 < 1.
//  - patches/compact-control-34.patch, 08-assembly eq:fixed-parameters and the
//    "remaining comparisons": eps < 1/3, 2 eps < 1, eps(1-tau) < 1-tau,
//    3/4 + delta + 5 eps/4 < 1, eps(1+c) < 1, eps + delta < 1, and the
//    displayed size exponents (alpha, gamma, K, ell, prime-interval ratio).
//  - upstream 07-resampling lem:no-sort-resampling: 0 < delta < 1/8.

import { type Q, q, add, sub, mul, max, min, eq, ONE, ZERO, twoPow } from "../rational";
import { margins as assemblyMargins, withKind, type Check, type Params } from "../parameters";

export type CompactParams = Params & { zeta: Q };

const TEN = (k: number) => 10n ** BigInt(k);

/** compact-control-note.tex, "Parameters and complete assembly" (also eq:fixed-parameters, patched). */
export function compactParams(): CompactParams {
  const a = q(296n, TEN(11));
  const ac = q(418n, TEN(12));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(1999n, 10000n),
    c: q(1n, 5n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(49961n, 10000n),
    lambda: sub(ONE, q(1671n, 4n * TEN(12))),
    lambdaPrime: sub(ONE, q(167n, 4n * TEN(11))),
    kappa: q(83n, TEN(12)),
  };
}

/**
 * Layer exponents (compact-control-layout.tex, "Unrolling"):
 *   chi      = tau + (1-beta) max{sigma - tau, 0}   internal levels, no K^tau factor
 *   leaf     = sigma + beta (1 - sigma)               stopped leaves
 *   reserve  = max{1 - c, 0}                          reservation preprocessing
 * `spacing` adds theta*c to chi: theta = 0 for the compact primitive; theta = tau
 * models the earlier wide-slot primitive with its K^tau factor (used only in tests).
 */
export function layerExponents(p: CompactParams, theta: Q = ZERO) {
  const chi = add(add(p.tau, mul(sub(ONE, p.beta), max(sub(p.sigma, p.tau), ZERO))), mul(theta, p.c));
  const leaf = add(p.sigma, mul(p.beta, sub(ONE, p.sigma)));
  const reserve = max(sub(ONE, p.c), ZERO);
  return { chi, leaf, reserve, layer: max(chi, leaf, reserve, ZERO) };
}

/** The seven margins have the same form as before (compact-control-note.tex; eq:margin-list, patched). */
export const compactMargins = (p: CompactParams) => assemblyMargins(p);

export function compactMinimumMargin(p: CompactParams): Q {
  return min(...Object.values(compactMargins(p)));
}

const LAY = "compact-control-layout.tex Unrolling / prop:simultaneous-layer (patched)";
const ASM = "compact-control-34.patch 08-assembly remaining comparisons";
const SET = "compact-control-34.patch 08-assembly size exponents";
const NOTE = "compact-control-note.tex sec. Parameters and complete assembly";

/**
 * Every inequality on the fixed rational parameters. The names in brackets are
 * the corresponding `constraint_slacks` keys of certificates/compact-control-layer.json
 * (mapped after the list was written from the note and patch).
 */
export function compactParameterChecks(p: CompactParams, theta: Q = ZERO): Check[] {
  const { tau, sigma, beta, zeta, epsilon: e, delta, C1, c, lambda, lambdaPrime: lp, kappa } = p;
  const x = layerExponents(p, theta);
  const half = q(1n, 2n);
  return withKind("condition", [
    { name: "tau > 0", source: LAY, lhs: ZERO, rel: "<", rhs: tau },
    { name: "tau < 1", source: LAY, lhs: tau, rel: "<", rhs: ONE },
    { name: "sigma > 0", source: LAY, lhs: ZERO, rel: "<", rhs: sigma },
    { name: "sigma < 1", source: LAY, lhs: sigma, rel: "<", rhs: ONE },
    { name: "beta > 0", source: LAY + ": rational 0 < beta < 1", lhs: ZERO, rel: "<", rhs: beta },
    { name: "beta < 1", source: LAY, lhs: beta, rel: "<", rhs: ONE },
    { name: "zeta > 0", source: "compact-control-guard.tex: zeta > 0", lhs: ZERO, rel: "<", rhs: zeta },
    { name: "c > 0", source: LAY + ": positive rationals", lhs: ZERO, rel: "<", rhs: c },
    { name: "epsilon > 0", source: LAY, lhs: ZERO, rel: "<", rhs: e },
    { name: "tau < lambda", source: LAY + ": max{tau,sigma,chi} < lambda", lhs: tau, rel: "<", rhs: lambda },
    { name: "sigma < lambda", source: LAY + ": max{tau,sigma,chi} < lambda", lhs: sigma, rel: "<", rhs: lambda },
    { name: "chi < lambda", source: LAY + ": max{tau,sigma,chi} < lambda (internal levels)", lhs: x.chi, rel: "<", rhs: lambda },
    { name: "lambda < lambda'", source: LAY, lhs: lambda, rel: "<", rhs: lp },
    { name: "lambda' < 1", source: LAY, lhs: lp, rel: "<", rhs: ONE },
    { name: "lambda < 1", source: LAY + " (implied by lambda < lambda' < 1)", lhs: lambda, rel: "<", rhs: ONE, kind: "implied" },
    { name: "sigma + beta(1-sigma) < lambda'", source: LAY + ": leaf exponent", lhs: x.leaf, rel: "<", rhs: lp },
    { name: "max{1-c,0} < lambda'", source: LAY + ": reservation exponent", lhs: x.reserve, rel: "<", rhs: lp },
    { name: "0 < lambda'", source: LAY + ": max{...,0} < lambda' (implied by 0 < tau < lambda < lambda')", lhs: ZERO, rel: "<", rhs: lp, kind: "implied" },
    { name: "epsilon*C1 < 1", source: LAY + " and compact-control-guard.tex (widths O(p))", lhs: mul(e, C1), rel: "<", rhs: ONE },
    { name: "epsilon < 1/3", source: ASM, lhs: e, rel: "<", rhs: q(1n, 3n) },
    { name: "2*epsilon < 1", source: ASM + " (prime selection)", lhs: mul(q(2n), e), rel: "<", rhs: ONE },
    { name: "epsilon(1-tau) < 1-tau", source: ASM + " (g4 > 0)", lhs: mul(e, sub(ONE, tau)), rel: "<", rhs: sub(ONE, tau) },
    {
      name: "3/4 + delta + 5*epsilon/4 < 1",
      source: ASM + " (g5 > 0, Gaussian line maps)",
      lhs: add(add(q(3n, 4n), delta), mul(q(5n, 4n), e)),
      rel: "<",
      rhs: ONE,
    },
    { name: "epsilon(1+c) < 1", source: ASM + " (g1 > 0; K = o(ell))", lhs: mul(e, add(ONE, c)), rel: "<", rhs: ONE },
    { name: "epsilon + delta < 1", source: ASM + " (g6 > 0)", lhs: add(e, delta), rel: "<", rhs: ONE },
    { name: "delta > 0", source: "07-resampling lem:no-sort-resampling: delta in (0,1/8)", lhs: ZERO, rel: "<", rhs: delta },
    { name: "delta < 1/8", source: "07-resampling lem:no-sort-resampling: delta in (0,1/8)", lhs: delta, rel: "<", rhs: q(1n, 8n) },
    { name: "alpha exponent 1/4+epsilon/4 < 1/2", source: SET + " (2 <= alpha < sqrt p)", lhs: add(q(1n, 4n), mul(q(1n, 4n), e)), rel: "<", rhs: half },
    { name: "gamma exponent 1/2+3*epsilon/2 < 1", source: SET + " (gamma = o(p))", lhs: add(half, mul(q(3n, 2n), e)), rel: "<", rhs: ONE },
    { name: "epsilon*c > 0", source: SET + " (K/log p -> oo)", lhs: ZERO, rel: "<", rhs: mul(e, c) },
    { name: "epsilon*c < 1 - epsilon", source: SET + " (K = o(ell))", lhs: mul(e, c), rel: "<", rhs: sub(ONE, e) },
    { name: "1 - epsilon > 0", source: SET + " (r superpolynomial)", lhs: ZERO, rel: "<", rhs: sub(ONE, e) },
    { name: "kappa > 0", source: NOTE, lhs: ZERO, rel: "<", rhs: kappa },
  ]);
}

/** The final assembly comparisons (compact-control-note.tex). */
export function compactMarginChecks(p: CompactParams): Check[] {
  const g = compactMargins(p);
  const G = compactMinimumMargin(p);
  return withKind("condition", [
    ...Object.entries(g).map(([k, gk]) => ({
      name: `kappa < ${k}`,
      source: "current-status.md: all seven final margins exceed kappa",
      lhs: p.kappa,
      rel: "<" as const,
      rhs: gk,
    })),
    { name: "kappa < G_* = min g_j (strict absorption gap)", source: NOTE + " (implied by the seven rows above)", lhs: p.kappa, rel: "<", rhs: G, kind: "implied" },
    { name: "kappa > 2^-34", source: NOTE + ": 2^-34 < 83/10^12", lhs: twoPow(-34), rel: "<", rhs: p.kappa },
    { name: "kappa < 2^-33", source: NOTE + ": 83/10^12 < 2^-33", lhs: p.kappa, rel: "<", rhs: twoPow(-33) },
  ]);
}

/** Displayed values of the note that are recomputed from the parameters, as equalities. */
export function compactStatedValues(p: CompactParams) {
  const e = p.epsilon;
  const x = layerExponents(p);
  const g = compactMargins(p);
  const G = compactMinimumMargin(p);
  const TEN15 = 4n * TEN(15);
  return [
    { name: "eps C1 = 99872039/10^8", source: NOTE, got: mul(e, p.C1), stated: q(99872039n, TEN(8)) },
    { name: "chi_reserve = 1 - c = 4/5", source: NOTE, got: x.reserve, stated: q(4n, 5n) },
    { name: "alpha exponent 1/4 + eps/4 = 11999/40000", source: NOTE, got: add(q(1n, 4n), mul(q(1n, 4n), e)), stated: q(11999n, 40000n) },
    { name: "gamma exponent 1/2 + 3 eps/2 = 15997/20000", source: NOTE, got: add(q(1n, 2n), mul(q(3n, 2n), e)), stated: q(15997n, 20000n) },
    { name: "prime-interval exponent 1 - 2 eps = 3001/5000", source: NOTE, got: sub(ONE, mul(q(2n), e)), stated: q(3001n, 5000n) },
    { name: "K exponent eps c = 1999/50000", source: SET, got: mul(e, p.c), stated: q(1999n, 50000n) },
    { name: "ell exponent 1 - eps = 8001/10000", source: SET, got: sub(ONE, e), stated: q(8001n, 10000n) },
    { name: "G_* = g3", source: NOTE, got: G, stated: g.g3 },
    { name: "G_* = 333833/(4*10^15)", source: NOTE, got: G, stated: q(333833n, TEN15) },
    { name: "G_* - kappa = 1833/(4*10^15)", source: NOTE, got: sub(G, p.kappa), stated: q(1833n, TEN15) },
  ].map((r) => ({ ...r, ok: eq(r.got, r.stated) }));
}
