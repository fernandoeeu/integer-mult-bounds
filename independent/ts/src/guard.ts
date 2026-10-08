// Stopped-depth guard bound, notes/stopped-guard.tex (sec:stopped-guard).
//
// With W = W_c, s = s_c of the complex network:
//   E = 64 (W + m + 1)^3,  B = s + E,  C0 = 128 m B^2,  C1 = 2,
//   Delta = ceil(C0 d^2).
// The note's argument needs these finite facts (all integer comparisons):
//   m >= 3,  2 <= s < m^5,
//   24 W^3 + 4 s + 4 W + 4 < E          (one invocation's arithmetic depth),
//   s (8 + E) <= 9 B^2                  (to pass from s(8+E)d^(5-4b) to 9B^2 d^(7/5)),
//   18 m B^2 + 18 <= 36 m B^2            (18mB^2 d^(19/10) + 18d <= 36mB^2 d^2 for d >= 1),
//   36 m B^2 < C0 = 128 m B^2            (final comparison with C0 d^2; a comparison of constants),
// and these exponent facts for rational 9/10 <= beta < 1:
//   5 - 4 beta <= 7/5,   7/5 + 1/2 <= C1 = 2   (the 2 m sqrt(d) pieces give d^(19/10) <= d^2),
// and the elementary 8d + t + 9 <= 18d for t = floor(D/2) <= d/2, d >= 1 (sampled below).
//
// Two of these comparisons hold for every positive input and therefore have no
// failure mode a test could exercise: s(8+E) <= 9B^2 (since 9(s+E)^2 >= 18sE >= sE + 8s
// when E >= 1) and 18mB^2 + 18 <= 36mB^2 (when mB^2 >= 1). They are evaluated and
// printed with kind "identity" and are not counted as checks; see README.

import { type Q, q, sub, mul, add } from "./rational";
import type { Check } from "./parameters";

export function guardConstants(W: bigint, s: bigint, m: bigint) {
  const E = 64n * (W + m + 1n) ** 3n;
  const B = s + E;
  const C0 = 128n * m * B * B;
  return { E, B, C0 };
}

const qi = (x: bigint) => q(x);

export function guardChecks(W: bigint, s: bigint, m: bigint, beta: Q, C1: Q): Check[] {
  const { E, B } = guardConstants(W, s, m);
  const src = "stopped-guard.tex";
  const onePiece = sub(q(5n), mul(q(4n), beta)); // exponent of d in s(8+E) d^(5-4 beta)
  return [
    { name: "m >= 3", source: src, lhs: q(3n), rel: "<=", rhs: qi(m) },
    { name: "s >= 2", source: src, lhs: q(2n), rel: "<=", rhs: qi(s) },
    { name: "s < m^5", source: src + " (so s^j <= s d^(5(1-beta)))", lhs: qi(s), rel: "<", rhs: qi(m ** 5n) },
    {
      name: "24W^3 + 4s + 4W + 4 < E",
      source: src + " (gates, child corrections, bank corrections)" + "; implied by 0 < s < W m (the positive rank deficit) and W >= 1",
      lhs: qi(24n * W ** 3n + 4n * s + 4n * W + 4n),
      rel: "<",
      rhs: qi(E),
      kind: "implied",
    },
    { name: "s(8+E) <= 9B^2", source: src + " (true for all s, E >= 1 since B = s + E)", lhs: qi(s * (8n + E)), rel: "<=", rhs: qi(9n * B * B), kind: "identity" },
    {
      name: "18 m B^2 + 18 <= 36 m B^2",
      source: src + " (18mB^2 d^(19/10) + 18d <= 36mB^2 d^2, d >= 1)",
      lhs: qi(18n * m * B * B + 18n),
      rel: "<=",
      rhs: qi(36n * m * B * B),
      kind: "identity", // true whenever m B^2 >= 1
    },
    {
      name: "36 < 128 (36 m B^2 < C0 = 128 m B^2)",
      source: src,
      lhs: q(36n),
      rel: "<",
      rhs: q(128n),
      kind: "constant",
    },
    {
      name: "beta >= 9/10 (guard)",
      source: src + ": every rational 9/10 <= beta < 1 (the same inequality as 5 - 4 beta <= 7/5 below, and as P2 beta >= 9/10)",
      lhs: q(9n, 10n),
      rel: "<=",
      rhs: beta,
      kind: "implied",
    },
    { name: "5 - 4 beta <= 7/5", source: src + " (one-piece depth exponent)", lhs: onePiece, rel: "<=", rhs: q(7n, 5n), kind: "condition" },
    {
      name: "7/5 + 1/2 <= C1",
      source: src + " (2 m sqrt(d) pieces of depth 9B^2 d^(7/5) give d^(19/10) <= d^C1)",
      lhs: add(q(7n, 5n), q(1n, 2n)),
      rel: "<=",
      rhs: C1,
      kind: "condition",
    },
  ];
}

/** 8d + floor(D/2) + 9 <= 18d for every 1 <= D <= d <= dMax (stopped-guard.tex, outer phases). */
export function outerPhaseChargeSampled(dMax: number): boolean {
  for (let d = 1; d <= dMax; d++) if (8 * d + (d >> 1) + 9 > 18 * d) return false; // integers, exact
  return true;
}

/**
 * Exact evaluation of the conservative depth recurrence from stopped-guard.tex
 *   A(e) <= s A(e/m) + E  at an internal node (e >= d^beta),   A(e) <= 8e at a leaf (e < d^beta),
 * taking equality at every step, for a root e = m^k <= d. The stopping test for
 * beta = u/v is the integer comparison e^v < d^u ("e^1000 < d^999").
 * Here d = m^K is an exact power of m, so the test on e = m^i is v*i < u*K and
 * no huge powers are formed. Returns A and the number j of internal levels.
 */
export function unrolledDepthAtPower(k: number, K: number, m: bigint, s: bigint, E: bigint, beta: Q) {
  if (k > K) throw new Error("root larger than d");
  const internal = (i: number) => !(beta.den * BigInt(i) < beta.num * BigInt(K));
  let j = 0;
  while (k - j >= 0 && internal(k - j)) j++;
  if (k - j < 0) throw new Error("recursion below a single chunk");
  let A = 8n * m ** BigInt(k - j); // leaf: 8u with u = m^(k-j)
  for (let i = 0; i < j; i++) A = s * A + E; // internal levels
  return { A, j };
}

/** The same recurrence for an arbitrary integer d, using the integer stopping test directly. */
export function unrolledDepth(k: number, d: bigint, m: bigint, s: bigint, E: bigint, beta: Q) {
  const isLeaf = (e: bigint) => e ** beta.den < d ** beta.num;
  let j = 0;
  while (k - j >= 0 && !isLeaf(m ** BigInt(k - j))) j++;
  if (k - j < 0) throw new Error("recursion below a single chunk");
  let A = 8n * m ** BigInt(k - j);
  for (let i = 0; i < j; i++) A = s * A + E;
  return { A, j };
}

/** Is A <= C * d^x for rational x = a/b > 0 ?  Compared as A^b <= C^b d^a. */
export function leConstTimesPower(A: bigint, C: bigint, d: bigint, x: Q): boolean {
  return A ** x.den <= C ** x.den * d ** x.num;
}
