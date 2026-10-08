// Generalized stopped-depth guard, notes/compact-control-guard.tex
// (sec:compact-stopped-guard), with the complex network's own m, W, s.
//
//   E = 64 (W + m + 1)^3,  B = s + E,  C1 = 5 - 4 beta + zeta,
//   C0 = ceil(max{128 m B^2, 18 m B^2 (1 + 1/zeta)}),  Delta = ceil(C0 d^C1).
//
// Finite facts the written argument uses (all exact comparisons):
//   m >= 3 and 2 <= s < m^5                          ("as checked below"; m >= 3 also gives log m > 1),
//   24 W^3 + 4 s + 4 W + 4 < E                        (retained from stopped-guard.tex: one invocation's depth),
//   s (8 + E) <= 9 B^2                                (A(e) <= s(8+E) d^(5-4beta) <= 9 B^2 d^(5-4beta)),
//   9 m B^2 (1 + 1/zeta) + 18 <= C0  and  C1 >= 1     (9mB^2(1+1/zeta) d^C1 + 18 d <= C0 d^C1 for d >= 1),
//   8d + floor(D/2) + 9 <= 18 d                       (outer phases; sampled),
// The first, the third, and the last hold for every admissible input (B = s + E,
// C0's definition, d >= 1); they are printed as identities and not counted.
// and the recurrence A(e) <= s A(e/m) + E internally, A(e) <= 8e at a leaf
// (e < d^beta), whose unrolling is evaluated exactly on samples below.
// The analytic step "at most m(1+1/zeta) d^zeta base-m pieces" (log d <= d^zeta/zeta)
// is not checked here.

import { type Q, q, add, sub, mul, div, max, ONE } from "../rational";
import type { Check } from "../parameters";

export function compactGuardConstants(W: bigint, s: bigint, m: bigint, zeta: Q) {
  const E = 64n * (W + m + 1n) ** 3n;
  const B = s + E;
  const mB2 = m * B * B;
  // zeta <= 0 is outside the note (the condition "zeta > 0" then fails); C0 is still
  // defined here, as 128 m B^2, so that a run with such a zeta reports instead of crashing
  const raw = zeta.num > 0n ? max(q(128n * mB2), mul(q(18n * mB2), add(ONE, div(ONE, zeta)))) : q(128n * mB2);
  const C0 = (raw.num + raw.den - 1n) / raw.den; // ceiling of a positive rational
  return { E, B, C0 };
}

export function compactGuardChecks(W: bigint, s: bigint, m: bigint, beta: Q, zeta: Q, C1: Q): Check[] {
  const { E, B, C0 } = compactGuardConstants(W, s, m, zeta);
  const src = "compact-control-guard.tex";
  const qi = (x: bigint) => q(x);
  return [
    { name: "m >= 3 (also gives log m > 1)", source: src, lhs: q(3n), rel: "<=", rhs: qi(m) },
    { name: "s >= 2", source: src, lhs: q(2n), rel: "<=", rhs: qi(s) },
    { name: "s < m^5", source: src + " (s^j <= s d^(5(1-beta)))", lhs: qi(s), rel: "<", rhs: qi(m ** 5n) },
    {
      name: "24W^3 + 4s + 4W + 4 < E",
      source: "stopped-guard.tex (retained node charge E for this network)" + "; implied by 0 < s < W m (the positive rank deficit) and W >= 1",
      lhs: qi(24n * W ** 3n + 4n * s + 4n * W + 4n),
      rel: "<",
      rhs: qi(E),
      kind: "implied",
    },
    { name: "s(8+E) <= 9B^2", source: src + " (one-piece constant; true for all s, E >= 1 since B = s + E)", lhs: qi(s * (8n + E)), rel: "<=", rhs: qi(9n * B * B), kind: "identity" },
    {
      name: "9 m B^2 (1 + 1/zeta) + 18 <= C0",
      source: src + " (whole-layer constant; d >= 1)",
      lhs: zeta.num > 0n ? add(mul(q(9n * m * B * B), add(ONE, div(ONE, zeta))), q(18n)) : q(C0 + 1n),
      rel: "<=",
      rhs: qi(C0),
      kind: "identity", // C0 >= 18 m B^2 (1 + 1/zeta) by definition, and 9 m B^2 (1 + 1/zeta) >= 18 when m B^2 >= 2
    },
    { name: "C1 >= 1 (so 18d <= 18 d^C1)", source: src + " (implied by C1 = 5 - 4 beta + zeta with beta < 1, zeta > 0)", lhs: ONE, rel: "<=", rhs: C1, kind: "implied" },
    { name: "C1 = 5 - 4 beta + zeta (<=)", source: src, lhs: C1, rel: "<=", rhs: add(sub(q(5n), mul(q(4n), beta)), zeta), kind: "condition" },
    { name: "C1 = 5 - 4 beta + zeta (>=)", source: src, lhs: add(sub(q(5n), mul(q(4n), beta)), zeta), rel: "<=", rhs: C1, kind: "condition" },
  ];
}

/**
 * Exact unrolled depth for every root e = m^k, k = 0..K, with d = m^K and
 * stopping test e < d^beta, i.e. beta.den * k < beta.num * K (the integer test
 * e^v < d^u of the note). Internal levels are contiguous, so A_k is computed
 * iteratively: A_k = 8 m^k at a leaf, A_k = s A_{k-1} + E internally.
 * Returns A_k and the number j_k of internal levels.
 */
export function depthTable(K: number, m: bigint, s: bigint, E: bigint, beta: Q) {
  const A: bigint[] = [];
  const j: number[] = [];
  for (let k = 0; k <= K; k++) {
    const leaf = beta.den * BigInt(k) < beta.num * BigInt(K);
    if (leaf) {
      A.push(8n * m ** BigInt(k));
      j.push(0);
    } else {
      if (k === 0) throw new Error("recursion below a single chunk");
      A.push(s * A[k - 1]! + E);
      j.push(j[k - 1]! + 1);
    }
  }
  return { A, j };
}

/**
 * For d = m^K with (5 - 4 beta) K an integer, check on every root e = m^k <= d:
 *   j <= (1 - beta) log_m d + 1,   A <= s(8+E) d^(5-4beta),   A <= 9 B^2 d^(5-4beta).
 */
export function depthSamplesAtPowers(Ks: number[], m: bigint, s: bigint, E: bigint, B: bigint, beta: Q) {
  const onePiece = sub(q(5n), mul(q(4n), beta));
  let ok = true;
  let cases = 0;
  let maxJ = 0;
  for (const K of Ks) {
    const expo = mul(onePiece, q(BigInt(K)));
    if (expo.den !== 1n) throw new Error("choose K with (5-4beta)K integral");
    const dPow = m ** expo.num; // d^(5-4beta) exactly
    const { A, j } = depthTable(K, m, s, E, beta);
    for (let k = 0; k <= K; k++) {
      cases++;
      maxJ = Math.max(maxJ, j[k]!);
      // j <= (1-beta) K + 1  <=>  beta.den (j - 1) <= (beta.den - beta.num) K
      const jOk = beta.den * BigInt(j[k]! - 1) <= (beta.den - beta.num) * BigInt(K);
      if (!(jOk && A[k]! <= s * (8n + E) * dPow && A[k]! <= 9n * B * B * dPow)) ok = false;
    }
  }
  return { ok, detail: `${cases} roots, up to ${maxJ} internal levels` };
}
