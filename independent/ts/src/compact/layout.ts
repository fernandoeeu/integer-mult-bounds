// Finite arithmetic from the reservation layout and the compact-control
// movement, derived from the written descriptions:
//
//  - notes/compact-control-layout.tex, "Rows and complete compact fields":
//      G = 4 ceil(log2 p) + 6,  H = d G,  q_F = ceil(2H/K),  q_B = ceil(H/K),
//      q_0 = ceil(log2 W) ceil(log_m(2d)),  k_0 = ceil(log_m d),  Q_0 = q_0 + q_F + q_B;
//      individual kernels if D <= Q_0; row range 2^(q_0 K) >= W^(k_0);
//      q_F + q_B <= 3dG/K + 2.
//  - notes/compact-control-movement.tex, "Guards and deterministic repair" and
//    prop:compact-selected-addition:
//      bad fraction delta = min{1, n (2 * 2^-G + 8 * 2^(G-K))},
//      and with K >= G + 4 ceil(log2 p) + 10, f <= p:  delta <= 5/(128 p^3).
//  - the same section, "Earlier source" and "Later source": the four-update
//    identity on an integer target segment v, a bit z and a dirty temporary w,
//      v <- v + 2 z w,  w <- w + (v mod 2),  v <- v + z(1 - 2w),  w <- w - ((v mod 2) xor z),
//    and the later-source composition through a loaded radix-B digit.
//
// What is NOT here: the full modular address permutation (swaps and rotations
// of packed fields), bad-set invariance and the repair sort. The repository's
// scripts/audit_compact_controls.py samples those; this checker does not.

import { type Q, q, add, mul, div, min, le, ONE } from "../rational";

/** Smallest j >= 0 with base^j >= n (n >= 1, base >= 2). */
export function ceilLog(n: bigint, base: bigint): number {
  if (n < 1n || base < 2n) throw new Error("ceilLog needs n >= 1, base >= 2");
  let j = 0;
  for (let power = 1n; power < n; power *= base) j++;
  return j;
}

/** G = 4 ceil(log2 p) + 6. */
export const guardWidth = (p: bigint) => 4 * ceilLog(p, 2n) + 6;

const ceilDiv = (a: bigint, b: bigint) => (a + b - 1n) / b;

/** Field sizes of the reservation layout for one node (no arrays are built). */
export function allocation(d: bigint, D: bigint, K: bigint, G: bigint, m: bigint, W: bigint) {
  if (!(1n <= D && D <= d && K >= 1n && G >= 1n)) throw new Error("invalid dimensions");
  const lgW = BigInt(ceilLog(W, 2n));
  const q0 = lgW * BigInt(ceilLog(2n * d, m));
  const k0 = BigInt(ceilLog(d, m));
  const H = d * G;
  const qF = ceilDiv(2n * H, K);
  const qB = ceilDiv(H, K);
  const Q0 = q0 + qF + qB;
  return {
    compact_capacity: H,
    row_chunks: q0,
    front_chunks: qF,
    back_chunks: qB,
    reserved_chunks: Q0,
    recursion_depth_cap: k0,
    row_bits: q0 * K,
    mode: D <= Q0 ? "individual" : "recursive",
    active_chunks: D > Q0 ? D - Q0 : 0n,
    preprocessed_chunks: D < Q0 ? D : Q0,
    front_slack_bits: qF * K - 2n * H,
    back_slack_bits: qB * K - H,
    // the facts the layout argument uses, as booleans
    rowRangeCoversWk0: q0 * K >= k0 * lgW, // 2^(q0 K) >= 2^(k0 ceil(log2 W)) >= W^k0
    frontFieldsFit: qF * K >= 2n * H,
    backFieldFits: qB * K >= H,
    reservedCountBound: le(q(qF + qB), add(div(q(3n * d * G), q(K)), q(2n))), // q_F + q_B <= 3dG/K + 2
  };
}

/** delta = min{1, n (2 * 2^-G + 8 * 2^(G-K))} and the uniform bound 5/(128 p^3). */
export function repairBound(p: bigint, n: bigint, K: bigint) {
  const G = BigInt(guardWidth(p));
  const ell = BigInt(ceilLog(p, 2n));
  const cutoff = K >= G + 4n * ell + 10n;
  const raw = mul(q(n), add(q(2n, 1n << G), q(8n, 1n << (K - G))));
  const delta = min(ONE, raw);
  const uniform = q(5n, 128n * p ** 3n);
  return { G, cutoff, delta, uniform, ok: le(delta, uniform) };
}

/** The four updates of the "Earlier source" paragraph, on integers. Returns final values and the largest |v - v0| seen. */
export function fourUpdates(v0: bigint, z: bigint, w0: bigint) {
  const par = (x: bigint) => ((x % 2n) + 2n) % 2n; // v mod 2 in {0,1}, also for negative v
  let v = v0;
  let w = w0;
  let maxDisp = 0n;
  const track = () => {
    const dd = v - v0 < 0n ? v0 - v : v - v0;
    if (dd > maxDisp) maxDisp = dd;
  };
  v = v + 2n * z * w;
  track();
  w = w + par(v);
  v = v + z * (1n - 2n * w);
  track();
  w = w - (par(v) ^ z);
  return { v, w, maxDisp };
}

export type DigitIdentityReport = { cases: number; identity: boolean; displacementWithin2B: boolean; loadWithinDigit: boolean; laterSourceParity: boolean };

/**
 * Exhaustive check of the stated algebra:
 *  (1) for all integers v in [-R, R], w in [-R, R], z in {0,1}: final v = v + z(1 - 2a), a = v mod 2, and w restored;
 *  (2) for G = 1..Gmax, B = 2^G and good digits w in [0, B-2]: the load w + (v mod 2) stays <= B - 1 and every
 *      intermediate displacement of v is at most 2B ("the target displacement is at most 2B");
 *  (3) later source: for good digits u in [0, B-2] and x in {0,1}, running the identity with control (u mod 2),
 *      loading u <- u + x (no overflow), running it with ((u + x) mod 2) and unloading toggles the parity of v by x
 *      and restores both temporaries.
 * With includeSaturated = true the digit B - 1 (which the note declares bad) is
 * included as well, so the failure mode the bad set excludes becomes visible.
 */
export function digitIdentityExhaustive(R: number, Gmax: number, includeSaturated = false): DigitIdentityReport {
  let cases = 0;
  let identity = true;
  let displacementWithin2B = true;
  let loadWithinDigit = true;
  let laterSourceParity = true;
  const par = (x: bigint) => ((x % 2n) + 2n) % 2n;
  for (let v = -R; v <= R; v++)
    for (let w = -R; w <= R; w++)
      for (const z of [0n, 1n]) {
        const V = BigInt(v);
        const r = fourUpdates(V, z, BigInt(w));
        cases++;
        if (r.v !== V + z * (1n - 2n * par(V)) || r.w !== BigInt(w)) identity = false;
      }
  for (let G = 1; G <= Gmax; G++) {
    const B = 1n << BigInt(G);
    const top = includeSaturated ? B - 1n : B - 2n; // largest digit value tried
    for (let w = 0n; w <= top; w++)
      for (let v = -4n * B; v <= 4n * B; v++)
        for (const z of [0n, 1n]) {
          cases++;
          if (w + par(v) > B - 1n) loadWithinDigit = false;
          if (fourUpdates(v, z, w).maxDisp > 2n * B) displacementWithin2B = false;
        }
    for (let u = 0n; u <= top; u++)
      for (const x of [0n, 1n])
        for (let v = -2n * B; v <= 2n * B; v++)
          for (let t = 0n; t <= top; t++) {
            cases++;
            const first = fourUpdates(v, par(u), t);
            const loaded = u + x; // load the selected bit of x into the digit u
            if (loaded > B - 1n) laterSourceParity = false;
            const second = fourUpdates(first.v, par(loaded), first.w);
            const unloaded = loaded - x;
            if (!(par(second.v) === (par(v) ^ x) && second.w === t && unloaded === u)) laterSourceParity = false;
          }
  }
  return { cases, identity, displacementWithin2B, loadWithinDigit, laterSourceParity };
}
