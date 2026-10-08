// Exact rational numbers on BigInt.
//
// A rational is a pair {num, den} with den > 0 and gcd(|num|, den) = 1.
// Every function returns a value in this normal form, so two rationals are
// equal exactly when their fields are equal. No floating point is used
// anywhere in this file.

export type Q = { readonly num: bigint; readonly den: bigint };

export function gcd(a: bigint, b: bigint): bigint {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) [x, y] = [y, x % y];
  return x;
}

export function q(num: bigint | number, den: bigint | number = 1n): Q {
  let n = BigInt(num);
  let d = BigInt(den);
  if (d === 0n) throw new Error("rational with zero denominator");
  if (d < 0n) [n, d] = [-n, -d];
  const g = gcd(n, d);
  return g > 1n ? { num: n / g, den: d / g } : { num: n, den: d };
}

/** Parse "p/q" or "p" (the format used by the repository's JSON certificates). */
export function parseQ(text: string): Q {
  const parts = text.trim().split("/");
  if (parts.length === 1) return q(BigInt(parts[0]!));
  if (parts.length === 2) return q(BigInt(parts[0]!), BigInt(parts[1]!));
  throw new Error(`not a rational: ${text}`);
}

export function show(x: Q): string {
  return x.den === 1n ? `${x.num}` : `${x.num}/${x.den}`;
}

export const ZERO = q(0n);
export const ONE = q(1n);

export const add = (x: Q, y: Q) => q(x.num * y.den + y.num * x.den, x.den * y.den);
export const sub = (x: Q, y: Q) => q(x.num * y.den - y.num * x.den, x.den * y.den);
export const mul = (x: Q, y: Q) => q(x.num * y.num, x.den * y.den);
export const neg = (x: Q) => q(-x.num, x.den);

export function div(x: Q, y: Q): Q {
  if (y.num === 0n) throw new Error("division by zero");
  return q(x.num * y.den, x.den * y.num);
}

/** x^k for an integer k (negative k allowed when x != 0). */
export function pow(x: Q, k: number): Q {
  if (k < 0) return div(ONE, pow(x, -k));
  const e = BigInt(k);
  return q(x.num ** e, x.den ** e);
}

/** Sign of x - y: -1, 0 or 1. Denominators are positive, so cross-multiplying is safe. */
export function cmp(x: Q, y: Q): -1 | 0 | 1 {
  const l = x.num * y.den;
  const r = y.num * x.den;
  return l < r ? -1 : l > r ? 1 : 0;
}

export const lt = (x: Q, y: Q) => cmp(x, y) < 0;
export const le = (x: Q, y: Q) => cmp(x, y) <= 0;
export const gt = (x: Q, y: Q) => cmp(x, y) > 0;
export const ge = (x: Q, y: Q) => cmp(x, y) >= 0;
export const eq = (x: Q, y: Q) => x.num === y.num && x.den === y.den;

export function min(...xs: Q[]): Q {
  if (xs.length === 0) throw new Error("min of nothing");
  return xs.reduce((best, x) => (lt(x, best) ? x : best));
}

export function max(...xs: Q[]): Q {
  if (xs.length === 0) throw new Error("max of nothing");
  return xs.reduce((best, x) => (gt(x, best) ? x : best));
}

export function sum(xs: Q[]): Q {
  return xs.reduce(add, ZERO);
}

/** 2^k as a rational, k may be negative. */
export const twoPow = (k: number) => (k >= 0 ? q(1n << BigInt(k)) : q(1n, 1n << BigInt(-k)));

/**
 * Decimal digits of a positive rational, truncated (not rounded) to `digits`
 * places. Used only for human-readable printing, never for a decision.
 */
export function toDecimal(x: Q, digits: number): string {
  const sign = x.num < 0n ? "-" : "";
  const n = x.num < 0n ? -x.num : x.num;
  const scaled = (n * 10n ** BigInt(digits)) / x.den;
  const s = scaled.toString().padStart(digits + 1, "0");
  return `${sign}${s.slice(0, s.length - digits)}.${s.slice(s.length - digits)}`;
}
