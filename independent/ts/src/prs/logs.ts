// Comparisons with rational exponents whose denominators are too large for
// exact integer powers (PR 1 uses epsilon = 1999999999999/10^13, so the
// note's own test d^(10^13) <= b^1999999999999 cannot be evaluated).
//
// Method: rigorous enclosures of natural logarithms (src/log.ts, atanh series
// with an explicit tail bound). A comparison is decided only when the two
// enclosures are separated; otherwise the function throws, so an undecided
// comparison can never be reported as true or false. Where the exact integer
// comparison is feasible, the tests check that both methods agree.

import { type Q, q, add, mul, lt, le, sub } from "../rational";
import { logIntegerEnclosure, logEnclosureNearOne, type Enclosure } from "../log";

const LOG2 = logEnclosureNearOne(q(2n), 40);

const logInt = (x: bigint): Enclosure => (x === 1n ? { lower: q(0n), upper: q(0n) } : logIntegerEnclosure(x, 40));

/** floor(2^x) for rational x >= 0: the largest integer d with d^den <= 2^(num), decided by enclosures. */
export function floorTwoPower(x: Q): bigint {
  if (x.num < 0n) throw new Error("floorTwoPower needs x >= 0");
  const j = x.num / x.den; // floor(x)
  // binary search for the largest d in [2^j, 2^(j+1)) with log d <= x log 2
  let lo = 1n << j;
  let hi = 1n << (j + 1n); // log hi > x log 2 since hi = 2^(j+1) > 2^x
  while (hi - lo > 1n) {
    const mid = (lo + hi) / 2n;
    if (logAtMostTwoPower(mid, x)) lo = mid;
    else hi = mid;
  }
  return lo;
}

/** Is log d <= x log 2, i.e. d <= 2^x ? Exact when d is a power of two; otherwise by enclosures. */
function logAtMostTwoPower(d: bigint, x: Q): boolean {
  if ((d & (d - 1n)) === 0n) {
    const k = BigInt(d.toString(2).length - 1);
    return le(q(k), x);
  }
  // d is not a power of two, so log2 d is irrational and never equals x
  const L = logInt(d);
  if (le(L.upper, mul(x, LOG2.lower))) return true;
  if (lt(mul(x, LOG2.upper), L.lower)) return false;
  throw new Error(`log comparison of ${d} with 2^${x.num}/${x.den} undecided`);
}

/** Is A < C * (2^k)^e ?  Decided by enclosures of log A, log C and log 2. */
export function lessThanTwoPowerTimes(A: bigint, C: bigint, k: number, e: Q): boolean {
  const LA = logInt(A);
  const LC = logInt(C);
  const rhsLower = add(LC.lower, mul(mul(e, q(BigInt(k))), LOG2.lower));
  const rhsUpper = add(LC.upper, mul(mul(e, q(BigInt(k))), LOG2.upper));
  if (lt(LA.upper, rhsLower)) return true;
  if (le(rhsUpper, LA.lower)) return false;
  throw new Error(`log comparison ${A} < ${C} 2^(${k} e) undecided`);
}

/** Width of the enclosure used for log 2 (for the report). */
export const log2Width = () => sub(LOG2.upper, LOG2.lower);
