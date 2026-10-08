// The downstream parameter system behind kappa = 2^-59.
//
// Sources:
//  - notes/paired-note.tex, section "Exact parameters and final margin"
//    (the parameter values, the layer conditions, the seven margins g1..g7,
//    and G = min g_j = g2 = g3 > 2^-59).
//  - patches/h50-paired-59.patch, hunk for 08-assembly.tex
//    (eq:fixed-parameters, the "dimension and cost comparisons", eq:margin-list).
//  - upstream 05-layers.tex "Unrolling the recurrence" and
//    prop:simultaneous-layer as patched (9/10 <= beta < 1, C1 = 2).
//  - upstream 08-assembly.tex eq:sizes and the asymptotic side conditions
//    restated at the end of paired-note.tex.
//
// Every check is a strict (or, where the source says so, non-strict)
// comparison of two exact rationals. Nothing here is rounded.

import { type Q, q, add, sub, mul, div, min, lt, le, ONE, ZERO, twoPow } from "./rational";

export type Params = {
  a: Q; // bit-network saving, tau = 1 - a
  ac: Q; // complex-network saving, sigma = 1 - ac
  tau: Q;
  sigma: Q;
  beta: Q;
  epsilon: Q;
  delta: Q;
  C1: Q;
  c: Q;
  lambda: Q;
  lambdaPrime: Q;
  kappa: Q;
};

const TEN11 = 10n ** 11n;

/** paired-note.tex, "Exact parameters and final margin". */
export function noteParams(): Params {
  return recipeParams(q(296n, TEN11), q(1n, TEN11));
}

/**
 * The note's recipe as a function of the two savings a, a_c (beta = 999/1000):
 * c = beta a, lambda = 1 - (1+beta) a^2 / 2, lambda' = 1 - beta a^2
 * (docs/research/paired-network.md, "Exact final parameters").
 */
export function recipeParams(a: Q, ac: Q): Params {
  const a2 = mul(a, a);
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    beta: q(999n, 1000n),
    epsilon: q(199n, 1000n),
    delta: q(1n, 10000n),
    C1: q(2n),
    c: mul(q(999n, 1000n), a),
    lambda: sub(ONE, mul(q(1999n, 2000n), a2)),
    lambdaPrime: sub(ONE, mul(q(999n, 1000n), a2)),
    kappa: twoPow(-59),
  };
}

/** The seven normalized cost margins, eq:margin-list as patched (paired-note.tex). */
export function margins(p: Params) {
  const { tau, epsilon: e, c, lambdaPrime, delta } = p;
  return {
    g1: sub(ONE, mul(e, add(ONE, c))), // prefix-slot moves:     1 - eps(1+c)
    g2: mul(mul(e, c), sub(ONE, tau)), // chunk exchanges:       eps c (1-tau)
    g3: mul(e, sub(ONE, lambdaPrime)), // simultaneous rounds:  eps (1-lambda')
    g4: mul(sub(ONE, tau), sub(ONE, e)), // CRT and axis layouts: (1-tau)(1-eps)
    g5: sub(sub(q(1n, 4n), delta), mul(q(5n, 4n), e)), // Gaussian line maps: 1/4 - delta - 5eps/4
    g6: sub(sub(ONE, delta), e), // chirps, scalar products: 1 - delta - eps
    g7: e, // packed polynomial products
  };
}

/**
 * The same seven margins derived from the rows of the patched cost table in
 * 08-assembly.tex (normalized cost per unit volume), using the size exponents
 * of eq:sizes and the Gaussian section: d = p^eps, K = p^(eps c),
 * ell = p^(1-eps), log r = p^(1-eps), alpha = p^(1/4 + eps/4).
 * Each margin is 1 minus the exponent of its row. `alphaExponent` is the
 * exponent of alpha in p; the default is the smaller width 1/4 + eps/4. The
 * upstream width alpha = ceil((12 d^2 b)^(1/4)) has exponent 1/4 + eps/2.
 */
export function marginsFromCostTable(p: Params, alphaExponent?: Q) {
  const { tau, epsilon: e, c, lambdaPrime, delta } = p;
  const d = e;
  const K = mul(e, c);
  const ell = sub(ONE, e);
  const alpha = alphaExponent ?? add(q(1n, 4n), mul(q(1n, 4n), e));
  const rows = {
    g1: add(d, K), //                                  d K
    g2: add(ONE, mul(K, sub(tau, ONE))), //            p K^(tau-1)
    g3: add(ell, mul(d, lambdaPrime)), //              ell d^lambda'
    g4: add(d, mul(tau, ell)), //                      d (1 + ell^tau)
    g5: add(add(d, add(q(1n, 2n), delta)), alpha), // d p^(1/2+delta) alpha
    g6: add(d, delta), //                              d p^delta
    g7: ell, //                                        log(r p) = O(p^(1-eps))
  };
  return Object.fromEntries(Object.entries(rows).map(([k, x]) => [k, sub(ONE, x)])) as Record<keyof typeof rows, Q>;
}

export function minimumMargin(p: Params): Q {
  return min(...Object.values(margins(p)));
}

/**
 * A comparison "lhs rel rhs". `kind` says what it can show:
 *  - "check" (default): involves a value this checker recomputes (a count, a
 *    rank deficit, a logarithm enclosure, a guard constant, a displayed exponent)
 *    and fails for some admissible change of the inputs (tests exercise each one);
 *  - "condition": a comparison the note states between its own input parameters
 *    (tau, sigma, beta, epsilon, ...). Nothing is recomputed; it fails when a
 *    parameter is moved past the stated limit. Counted separately from "check".
 *    Conditions are counted one per stated comparison and overlap logically
 *    (for example 2 eps < 1 follows from eps < 1/3);
 *  - "constant": compares numbers written inside a note's argument, independent
 *    of the witness parameters (it fails only if the note's constant is wrong);
 *  - "identity": holds for every admissible input (for example s(8+E) <= 9B^2
 *    with B = s + E), so it has no failure mode; printed, never counted;
 *  - "implied": the same inequality as, or an immediate consequence of, rows
 *    that are counted elsewhere; printed for the argument, never counted.
 */
export type Check = {
  name: string;
  source: string; // where the inequality is stated
  lhs: Q;
  rel: "<" | "<=";
  rhs: Q;
  kind?: "check" | "condition" | "constant" | "identity" | "implied";
};

/** Give every row without an explicit kind the kind `k`. */
export const withKind = (k: NonNullable<Check["kind"]>, rows: Check[]): Check[] => rows.map((r) => (r.kind ? r : { ...r, kind: k }));

export const holds = (k: Check) => (k.rel === "<" ? lt(k.lhs, k.rhs) : le(k.lhs, k.rhs));
export const slack = (k: Check) => sub(k.rhs, k.lhs);

/**
 * Every downstream inequality on the fixed rational parameters.
 * Each entry is "lhs rel rhs"; the whole list must hold.
 */
export function parameterChecks(p: Params): Check[] {
  const { tau, sigma, beta, epsilon: e, delta, C1, c, lambda, lambdaPrime: lp, kappa } = p;
  const g = margins(p);
  const G = minimumMargin(p);
  const half = q(1n, 2n);
  const L = "05-layers prop:simultaneous-layer (patched)";
  const A = "08-assembly eq:fixed-parameters comparisons (patched)";
  const S = "08-assembly eq:sizes / paired-note sec. 4 side conditions";
  return withKind("condition", [
    { name: "tau > 0", source: "05-layers Unrolling: 0<tau<1", lhs: ZERO, rel: "<", rhs: tau },
    { name: "tau < 1", source: "05-layers Unrolling: 0<tau<1", lhs: tau, rel: "<", rhs: ONE },
    { name: "sigma > 0", source: "05-layers Unrolling: max{0,log_m(s/W)}<=sigma", lhs: ZERO, rel: "<", rhs: sigma },
    { name: "sigma < 1", source: "05-layers Unrolling", lhs: sigma, rel: "<", rhs: ONE },
    { name: "beta >= 9/10", source: L + ": rational 9/10<=beta<1", lhs: q(9n, 10n), rel: "<=", rhs: beta },
    { name: "beta < 1", source: L, lhs: beta, rel: "<", rhs: ONE },
    { name: "c > 0", source: L + ": c positive", lhs: ZERO, rel: "<", rhs: c },
    { name: "epsilon > 0", source: L + ": epsilon positive", lhs: ZERO, rel: "<", rhs: e },
    { name: "tau < lambda", source: L + ": max{tau,sigma}<lambda", lhs: tau, rel: "<", rhs: lambda },
    { name: "sigma < lambda", source: L + ": max{tau,sigma}<lambda", lhs: sigma, rel: "<", rhs: lambda },
    { name: "lambda < 1", source: L + " (implied by lambda < lambda' < 1)", lhs: lambda, rel: "<", rhs: ONE, kind: "implied" },
    {
      name: "tau(1+c/beta) < lambda",
      source: L + " (packed overhead; note: tau(1+c/beta)=1-a^2)",
      lhs: mul(tau, add(ONE, div(c, beta))),
      rel: "<",
      rhs: lambda,
    },
    { name: "lambda < lambda'", source: L + ": max{lambda,...}<lambda'", lhs: lambda, rel: "<", rhs: lp },
    {
      name: "sigma + beta(1-sigma) < lambda'",
      source: L + " (leaf cost)",
      lhs: add(sigma, mul(beta, sub(ONE, sigma))),
      rel: "<",
      rhs: lp,
    },
    { name: "lambda' < 1", source: L, lhs: lp, rel: "<", rhs: ONE },
    { name: "epsilon*C1 < 1", source: L + " and stopped-guard.tex (guard width d^C1 = o(p))", lhs: mul(e, C1), rel: "<", rhs: ONE },
    { name: "epsilon < 1/3", source: A + " (gamma sublinear, Gaussian width section)", lhs: e, rel: "<", rhs: q(1n, 3n) },
    { name: "2*epsilon < 1", source: A + " (prime-interval selection)", lhs: mul(q(2n), e), rel: "<", rhs: ONE },
    { name: "epsilon(1-tau) < 1-tau", source: A + " (g4 > 0)", lhs: mul(e, sub(ONE, tau)), rel: "<", rhs: sub(ONE, tau) },
    {
      name: "3/4 + delta + 5*epsilon/4 < 1",
      source: A + " (g5 > 0, Gaussian line maps)",
      lhs: add(add(q(3n, 4n), delta), mul(q(5n, 4n), e)),
      rel: "<",
      rhs: ONE,
    },
    { name: "epsilon(1+c) < 1", source: A + " (g1 > 0; also K = o(ell))", lhs: mul(e, add(ONE, c)), rel: "<", rhs: ONE },
    { name: "epsilon + delta < 1", source: A + " (g6 > 0)", lhs: add(e, delta), rel: "<", rhs: ONE },
    { name: "delta > 0", source: "07-resampling lem:no-sort-resampling: delta in (0,1/8)", lhs: ZERO, rel: "<", rhs: delta },
    { name: "delta < 1/8", source: "07-resampling lem:no-sort-resampling: delta in (0,1/8)", lhs: delta, rel: "<", rhs: q(1n, 8n) },
    {
      name: "alpha exponent 1/4+epsilon/4 < 1/2",
      source: "paired-note sec. 3 (alpha < sqrt p eventually)",
      lhs: add(q(1n, 4n), mul(q(1n, 4n), e)),
      rel: "<",
      rhs: half,
    },
    {
      name: "gamma exponent 1/2+3*epsilon/2 < 1",
      source: "paired-note sec. 3 (gamma = o(p))",
      lhs: add(half, mul(q(3n, 2n), e)),
      rel: "<",
      rhs: ONE,
    },
    { name: "epsilon*c > 0", source: S + " (K = Theta(p^(eps c)), K/log p -> oo)", lhs: ZERO, rel: "<", rhs: mul(e, c) },
    { name: "epsilon*c < 1 - epsilon", source: S + " (K = o(ell), ell = Theta(p^(1-eps)))", lhs: mul(e, c), rel: "<", rhs: sub(ONE, e) },
    { name: "1 - epsilon > 0", source: S + " (r superpolynomial)", lhs: ZERO, rel: "<", rhs: sub(ONE, e) },
    // g_j > 0 for every j follows from 0 < kappa < G = min g_j (the two rows below)
    ...Object.entries(g).map(([k, gk]) => ({ name: `${k} > 0`, source: "eq:margin-list (patched); implied by 0 < kappa < G", lhs: ZERO, rel: "<" as const, rhs: gk, kind: "implied" as const })),
    { name: "kappa > 0", source: "08-assembly: 0 < kappa", lhs: ZERO, rel: "<", rhs: kappa },
    { name: "kappa < G = min g_j", source: "paired-note: G > 2^-59; rho = G - kappa > 0", lhs: kappa, rel: "<", rhs: G },
  ]);
}

/**
 * The recurrence comparisons s/W < m^tau (bit) and s_c/W_c < m^sigma (complex).
 * Source: paired-construction.tex "Explicit exponents at ground size fifty".
 * If log m < L0 and eta > a*L0 then m^(1-a) = m e^(-a log m) > m(1 - a L0) > m(1-eta) = s/W.
 * This uses e^(-x) > 1 - x, valid for every real x != 0.
 */
export function recurrenceChecks(etaB: Q, etaC: Q, L0: Q, logMUpper: Q, p: Params): Check[] {
  return [
    { name: "log m < L0", source: "paired-construction: log m <= 16(S(2)+E0(2)) + S(m/2^16)+E0(m/2^16) < L0", lhs: logMUpper, rel: "<", rhs: L0 },
    { name: "eta_b > a*L0", source: "paired-construction: eta_b^pair > a L0", lhs: mul(p.a, L0), rel: "<", rhs: etaB },
    { name: "eta_c > a_c*L0", source: "paired-construction: eta_c > a_c L0", lhs: mul(p.ac, L0), rel: "<", rhs: etaC },
  ];
}
