// The complex network's actual saving and the scoped ceiling,
// notes/compact-control-note.tex, paragraph "Earlier targets and the next ceiling".
//
// The supremal complex saving a* satisfies s/W = m^(1 - a*), i.e.
//   a* = -log(1 - eta) / log m,   eta = (W m - s)/(W m).
// Enclosure used here (not the Python's): the Mercator series
//   -log(1 - eta) = sum_{k>=1} eta^k / k,
// whose partial sum is a lower bound and whose tail after K terms is at most
//   eta^(K+1) / ((K+1)(1 - eta)),
// combined with the atanh enclosure of log m (log.ts).
//
// Scoped ceiling argument of the note, each step a finite comparison here:
//   kappa < G_* <= g3 = eps (1 - lambda'),
//   g5 > 0 gives eps < 1/5,
//   the leaf condition gives 1 - lambda' < (1 - beta)(1 - sigma) < 1 - sigma = a_c,
//   a_c < a*  (the recurrence needs s/W < m^sigma),
// hence kappa < a*/5 <= upper/5, which the note bounds by 8.369598075e-11 < 2^-33.

import { type Q, q, add, sub, mul, div, pow, ONE } from "../rational";
import type { Enclosure } from "../log";

/** [lower, upper] for -log(1 - x), 0 < x < 1, using `terms` terms of the Mercator series. */
export function minusLogOneMinusEnclosure(x: Q, terms = 4): Enclosure {
  let s = q(0n);
  for (let k = 1; k <= terms; k++) s = add(s, div(pow(x, k), q(k)));
  const tail = div(pow(x, terms + 1), mul(q(terms + 1), sub(ONE, x)));
  return { lower: s, upper: add(s, tail) };
}

/** Enclosure of a* = -log(1-eta)/log m from enclosures of the numerator and of log m. */
export function savingEnclosure(eta: Q, logm: Enclosure): Enclosure {
  const num = minusLogOneMinusEnclosure(eta);
  return { lower: div(num.lower, logm.upper), upper: div(num.upper, logm.lower) };
}
