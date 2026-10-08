// Wire counts, rank sums and relative rank deficits of the two finite networks.
//
// Sources (all formulas are re-typed from the TeX, not from the Python):
//  - upstream/build/sections/03-motifs.tex: v = C(h,3), N = v^3, m = h^3,
//    I = 3v^2 invocations, neighbour counts z_b, z_c, wire counts
//    (eq:bit-wire-count, eq:complex-wire-count), rank sums in
//    prop:bit-motif-interface and prop:complex-motif-interface, and the
//    relative deficits eta = (Wm - s)/(Wm).
//  - notes/parameter-note.tex, section "Changing the common recurrence
//    exponent": the same formulas written for general h, with L_b = I h^2 and
//    L_c = I h (h+1).
//  - notes/paired-construction.tex, prop:paired-bit-interface: the new bit
//    network W = 2N + 2 v^2 (R + h), s = W m - N + 6 v^2 h^2.

import { binom } from "./intmath";
import { type Q, q } from "./rational";

export function ground(h: number) {
  const H = BigInt(h);
  const v = binom(H, 3n); // number of triples of the ground set [h]
  return { h: H, v, N: v ** 3n, m: H ** 3n, I: 3n * v * v };
}

/** Complex motif, original construction (03-motifs.tex), unchanged at h = 50. */
export function complexNetwork(h: number) {
  const { v, N, m, I, h: H } = ground(h);
  const z = binom(H - 3n, 3n) + 3n * (H - 3n); // neighbours: intersection 0 and 2
  const W = 2n * N + I * (v * z + H + 1n); // eq:complex-wire-count, c_c = h + 1
  const L = I * H * (H + 1n); // total decreasing dimension
  const s = W * m - 2n * N + 2n * L; // prop:complex-motif-interface
  const deficit = W * m - s; // = 2N - 2L
  return { z, W, L, s, deficit, eta: q(deficit, W * m), lossOverN: q(L, N) };
}

/** Bit motif, original construction (03-motifs.tex). Kept for the displayed counts. */
export function originalBitNetwork(h: number) {
  const { v, N, m, I, h: H } = ground(h);
  const z = 3n * binom(H - 3n, 2n); // intersection-one neighbours
  const W = 2n * N + I * (v * z + H); // eq:bit-wire-count, c_b = h
  const L = I * H * H;
  const s = W * m - N + 2n * L; // prop:bit-motif-interface
  const deficit = W * m - s; // = N - 2L
  return { z, W, L, s, deficit, eta: q(deficit, W * m), lossOverN: q(L, N), sideRoles: v * z };
}

/**
 * Paired-block bit network (prop:paired-bit-interface). R is the number of
 * side roles per invocation, recomputed from the circuit in circuit.ts.
 * Stage 1 and stage 3 share their complete auxiliary banks, which is why the
 * auxiliary count carries 2 v^2 rather than 3 v^2 invocations.
 */
export function pairedBitNetwork(h: number, R: bigint) {
  const { v, N, m, h: H } = ground(h);
  const W = 2n * N + 2n * v * v * (R + H);
  const L = 3n * v * v * H * H; // "the total decreasing dimension is 3 v^2 h^2"
  const s = W * m - N + 2n * L;
  const deficit = W * m - s; // = N - 6 v^2 h^2, independent of R
  return { W, L, s, deficit, eta: q(deficit, W * m) as Q };
}
