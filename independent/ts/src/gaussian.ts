// The smaller Gaussian width, paired-note.tex section "A smaller Gaussian width"
// and the 08-assembly hunk of patches/h50-paired-59.patch (eq:gamma). The same
// width is retained by notes/compact-control-note.tex (section "Parameters and
// complete assembly") and patches/compact-control-34.patch (eq:gamma).
//
//   p = 6b,  eta = 1/(4d),  theta_i > 1/(4d),
//   alpha = ceil((32 d b)^(1/4)),  gamma = 2 d alpha^2,
//   alpha^4 theta_i > 8b > p,
//   alpha <= 2 (32 d b)^(1/4),  gamma < 46 d^(3/2) sqrt(b),
//   d = floor(b^epsilon) <= b^epsilon  =>  gamma < 46 b^(1/2 + 3 eps/2),
//   b >= 2^40  =>  46 b^(1/2 + 3 eps/2) <= b/4.
//
// With eps = 199/1000 the exponent is 1597/2000 and the cutoff is certified by
// 184^2000 < 2^16120 (paired note). With eps = 1999/10000 it is 15997/20000; the
// compact-control note argues "since eps < 1/5, ... indeed 184 < 2^8".
//
// Everything below is integer arithmetic. "x^(1/4)" is never evaluated; it is
// compared through fourth powers.

import { ceilRoot, floorRoot } from "./intmath";
import { type Q, q, add, mul, le, ONE } from "./rational";
import type { Check } from "./parameters";

/** alpha and gamma for given integers d, b >= 1 (alpha may be overridden to test failure modes). */
export function gaussianWidth(d: bigint, b: bigint, alpha = ceilRoot(32n * d * b, 4)) {
  return { alpha, gamma: 2n * d * alpha * alpha };
}

/** d = floor(b^(u/v)) found as the largest d with d^v <= b^u (08-assembly setup, patched). */
export function dimensionFromB(b: bigint, epsilon: Q): bigint {
  return floorRoot(b ** epsilon.num, Number(epsilon.den));
}

/** Exponent of b in the bound on gamma: 1/2 + 3 eps / 2. */
export const gammaExponent = (epsilon: Q) => add(q(1n, 2n), mul(q(3n, 2n), epsilon));

/**
 * Pointwise facts for one pair (d, b). Each line is a plain integer comparison:
 *  - alpha^4 >= 32 d b                      (definition of the ceiling)
 *  - alpha^4 / (4d) >= 8b                    (so alpha^4 theta > 8b when theta > 1/(4d))
 *  - 8b > 6b = p
 *  - alpha^4 <= 16 * 32 d b                  (alpha <= 2 (32db)^(1/4))
 *  - gamma^2 < 46^2 d^3 b                    (gamma < 46 d^(3/2) sqrt b)
 */
export function gaussianPointChecks(d: bigint, b: bigint, alphaOverride?: bigint) {
  const { alpha, gamma } = gaussianWidth(d, b, alphaOverride);
  const a4 = alpha ** 4n;
  return {
    alpha,
    gamma,
    alphaFourthCovers: a4 >= 32n * d * b,
    resamplingMargin: a4 >= 8n * b * 4n * d, // alpha^4/(4d) >= 8b
    eightBAboveP: 8n * b > 6n * b,
    alphaAtMostTwiceRoot: a4 <= 16n * 32n * d * b,
    gammaBelow46: gamma * gamma < 46n * 46n * d ** 3n * b,
  };
}

/**
 * Does b >= 2^cutoffExp imply 46 b^e <= b/4, e = gammaExponent(eps) = u/v?
 * Equivalent to 184 <= b^((v-u)/v), and b^((v-u)/v) >= 2^(cutoffExp (v-u)/v),
 * so it suffices (and, for b = 2^cutoffExp, is necessary) that 184^v <= 2^(cutoffExp (v-u)).
 */
export function cutoffSuffices(epsilon: Q, cutoffExp: bigint): boolean {
  const e = gammaExponent(epsilon);
  return le(q(184n ** e.den), pow2(cutoffExp * (e.den - e.num)));
}

/** 2^k as a rational for any integer k (k < 0 occurs when the gamma exponent is at least 1). */
const pow2 = (k: bigint) => (k >= 0n ? q(2n ** k) : q(1n, 2n ** -k));

/**
 * The Gaussian-section comparisons for a given epsilon. `stated` is the
 * exponent of gamma written in the note (1597/2000 or 15997/20000).
 * `widthConstant` is the constant written in eq:gamma (46).
 */
export function gaussianChecks(epsilon: Q, stated: Q, source: string, widthConstant = 46n): Check[] {
  const e = gammaExponent(epsilon);
  return [
    // gamma = 2 d alpha^2 <= 2d * 4 sqrt(32 d b) = 8 sqrt(32) d^(3/2) sqrt b, and (8 sqrt 32)^2 = 2048
    {
      name: "(8*sqrt(32))^2 = 2048 < C^2 for the constant C of eq:gamma",
      source,
      lhs: q(2048n),
      rel: "<",
      rhs: q(widthConstant * widthConstant), // C = 46 in the note
      kind: "constant",
    },
    { name: "gamma exponent 1/2 + 3 eps/2 <= the stated exponent", source, lhs: e, rel: "<=", rhs: stated },
    { name: "gamma exponent 1/2 + 3 eps/2 >= the stated exponent", source, lhs: stated, rel: "<=", rhs: e },
    {
      // with e = u/v: 46 b^e <= b/4 for all b >= 2^40 iff 184^v <= 2^(40 (v - u))
      name: "b >= 2^40 gives 46 b^e <= b/4 (e = 1/2 + 3 eps/2 = u/v): 184^v <= 2^(40(v-u))",
      source,
      lhs: q(184n ** e.den),
      rel: "<=",
      rhs: pow2(40n * (e.den - e.num)),
    },
    // the next two are the same inequalities as the parameter conditions
    // "gamma exponent 1/2+3*epsilon/2 < 1" and "alpha exponent 1/4+epsilon/4 < 1/2"
    { name: "gamma exponent < 1 (gamma = o(p))", source: source + " (same as the parameter condition)", lhs: e, rel: "<", rhs: ONE, kind: "implied" },
    {
      name: "alpha exponent 1/4 + eps/4 < 1/2 (alpha < sqrt p)",
      source: source + " (same as the parameter condition)",
      lhs: add(q(1n, 4n), mul(q(1n, 4n), epsilon)),
      rel: "<",
      rhs: q(1n, 2n),
      kind: "implied",
    },
  ];
}

/** Instances b = 2^k with d = floor(b^eps): every pointwise bound and the two bounds in terms of b. */
export function gaussianInstance(k: number, epsilon: Q) {
  const b = 1n << BigInt(k);
  const d = dimensionFromB(b, epsilon);
  const pc = gaussianPointChecks(d, b);
  const e = gammaExponent(epsilon);
  const ok =
    pc.alphaFourthCovers &&
    pc.resamplingMargin &&
    pc.eightBAboveP &&
    pc.alphaAtMostTwiceRoot &&
    pc.gammaBelow46 &&
    pc.alpha >= 2n &&
    pc.alpha * pc.alpha < 6n * b && // alpha < sqrt p, p = 6b
    4n * pc.gamma <= b && // gamma <= b/4
    pc.gamma ** e.den < 46n ** e.den * b ** e.num; // gamma < 46 b^e
  return { b, d, ...pc, ok };
}
