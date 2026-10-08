// Small exact integer helpers on BigInt.

export function binom(n: bigint | number, k: bigint | number): bigint {
  const N = BigInt(n);
  let K = BigInt(k);
  if (K < 0n || K > N) return 0n;
  if (K > N - K) K = N - K;
  let r = 1n;
  for (let i = 1n; i <= K; i++) r = (r * (N - K + i)) / i; // exact at every step
  return r;
}

/** floor(x^(1/k)) for x >= 0, by bisection on exact integer powers. */
export function floorRoot(x: bigint, k: number): bigint {
  if (x < 0n) throw new Error("floorRoot of a negative number");
  const K = BigInt(k);
  let lo = 0n;
  let hi = 1n;
  while (hi ** K <= x) hi *= 2n;
  // invariant: lo^k <= x < hi^k
  while (hi - lo > 1n) {
    const mid = (lo + hi) / 2n;
    if (mid ** K <= x) lo = mid;
    else hi = mid;
  }
  return lo;
}

/** ceil(x^(1/k)) for x >= 0. */
export function ceilRoot(x: bigint, k: number): bigint {
  const r = floorRoot(x, k);
  return r ** BigInt(k) === x ? r : r + 1n;
}

/** floor(log2 x) for x >= 1. */
export function floorLog2(x: bigint): number {
  if (x < 1n) throw new Error("floorLog2 needs x >= 1");
  return x.toString(2).length - 1;
}
