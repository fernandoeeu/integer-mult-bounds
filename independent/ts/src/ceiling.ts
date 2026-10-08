// How much room the published numbers leave, computed exactly.
//
// 1. Fixed-network ceiling (docs/research/paired-network.md, "What happened to
//    the earlier ceiling?"). With tau = 1 - a the margins obey
//      G <= g2 = eps c a,  c < beta a/(1-a) < a/(1-a)   (from tau(1+c/beta) < lambda < 1),
//      eps < 1/5                                         (from g5 = 1/4 - delta - 5eps/4 > 0),
//    so G < a^2/(5(1-a)). And a itself is below the supremum
//      a* = -log(1 - eta_b)/log m   (from s/W < m^tau, i.e. 1 - eta_b < m^(-a)).
//    Using -log(1-eta) <= eta/(1-eta) and a lower bound for log m gives an
//    upper bound a_up >= a*, and a^2/(5(1-a)) is increasing in a on (0,1).
//    The certificate states the resulting value is below 2^-58.
//
// 2. Role slack: the largest number of side roles R for which the published
//    inequality eta_b > a L0 would still hold.
//
// 3. The largest bit/complex savings on the 1/10^11 grid allowed by eta > a L0.

import { type Q, q, mul, div, sub, ONE } from "./rational";
import { minusLogOneMinusUpper } from "./log";
import { ground } from "./networks";

export function fixedNetworkCeiling(etaB: Q, logMLower: Q) {
  const aUpper = div(minusLogOneMinusUpper(etaB), logMLower);
  const value = div(mul(aUpper, aUpper), mul(q(5n), sub(ONE, aUpper)));
  return { aUpper, value };
}

/** Largest integer R with eta_b(R) > a * L0, eta_b(R) = (N - 6 v^2 h^2) / ((2N + 2 v^2 (R + h)) m). */
export function maxSideRoles(h: number, a: Q, L0: Q): bigint {
  const { v, N, m, h: H } = ground(h);
  const D = N - 6n * v * v * H * H;
  // eta > a L0  <=>  W < D / (m a L0)  <=>  2 v^2 (R + h) < D/(m a L0) - 2N
  const bound = sub(div(sub(div(q(D), mul(q(m), mul(a, L0))), q(2n * N)), q(2n * v * v)), q(H));
  // largest integer strictly below `bound`
  const fl = bound.num >= 0n ? bound.num / bound.den : -((-bound.num + bound.den - 1n) / bound.den);
  return fl * bound.den === bound.num ? fl - 1n : fl;
}

/** Largest k with eta > (k / unit) * L0. */
export function largestGridSaving(eta: Q, L0: Q, unit: bigint): bigint {
  const x = mul(div(eta, L0), q(unit));
  const fl = x.num / x.den;
  return fl * x.den === x.num ? fl - 1n : fl;
}
