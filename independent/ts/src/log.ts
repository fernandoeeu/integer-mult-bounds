// Rigorous rational enclosures of natural logarithms, and an exponential
// lower bound used as a second, independent route to the same comparison.
//
// Source: paired-construction.tex, subsection "Explicit exponents at ground
// size fifty". For 1 <= x <= 2 put z = (x-1)/(x+1). Then
//
//   log x = 2 * sum_{j>=0} z^(2j+1)/(2j+1)          (atanh series, 0 <= z < 1)
//
// Every term is >= 0, so a partial sum S(x) is a lower bound. The tail after
// J terms is at most 2 z^(2J+1)/(2J+1) * (1 + z^2 + z^4 + ...) =
// 2 z^(2J+1) / ((2J+1)(1 - z^2)) =: E0(x), so S(x) + E0(x) is an upper bound.
// The note uses J = 24 (j = 0..23, tail exponent 49).

import { type Q, q, add, mul, div, sub, pow, ONE, ZERO, le } from "./rational";
import { floorLog2 } from "./intmath";

export type Enclosure = { lower: Q; upper: Q };

/** [S(x), S(x)+E0(x)] for 1 <= x <= 2, with `terms` series terms (note: 24). */
export function logEnclosureNearOne(x: Q, terms = 24): Enclosure {
  if (!(le(ONE, x) && le(x, q(2n)))) throw new Error("logEnclosureNearOne needs 1 <= x <= 2");
  const z = div(sub(x, ONE), add(x, ONE));
  let s = ZERO;
  for (let j = 0; j < terms; j++) s = add(s, div(pow(z, 2 * j + 1), q(2 * j + 1)));
  const S = mul(q(2n), s);
  const tailExp = 2 * terms + 1;
  const E0 = div(mul(q(2n), pow(z, tailExp)), mul(q(tailExp), sub(ONE, mul(z, z))));
  return { lower: S, upper: add(S, E0) };
}

/**
 * Enclosure of log m for an integer m >= 1, written as m = 2^k * x with
 * 1 <= x < 2, so log m = k log 2 + log x (note: k = 16 for m = 125000).
 */
export function logIntegerEnclosure(m: bigint, terms = 24): Enclosure & { k: number; x: Q } {
  const k = floorLog2(m);
  const x = q(m, 1n << BigInt(k));
  const log2 = logEnclosureNearOne(q(2n), terms);
  const logx = logEnclosureNearOne(x, terms);
  return {
    k,
    x,
    lower: add(mul(q(k), log2.lower), logx.lower),
    upper: add(mul(q(k), log2.upper), logx.upper),
  };
}

/**
 * Lower bound for e^x when x >= 0: the Taylor partial sum sum_{k<=K} x^k/k!
 * (all omitted terms are non-negative). This is a different method from the
 * atanh series above; it is used to confirm log m < L0 by showing e^L0 > m.
 */
export function expLowerBound(x: Q, K: number): Q {
  if (x.num < 0n) throw new Error("expLowerBound needs x >= 0");
  let term = ONE;
  let s = ONE;
  for (let k = 1; k <= K; k++) {
    term = div(mul(term, x), q(k));
    s = add(s, term);
  }
  return s;
}

/** Upper bound for -log(1-eta), 0 <= eta < 1: -log(1-eta) = log(1 + eta/(1-eta)) <= eta/(1-eta). */
export function minusLogOneMinusUpper(eta: Q): Q {
  return div(eta, sub(ONE, eta));
}
