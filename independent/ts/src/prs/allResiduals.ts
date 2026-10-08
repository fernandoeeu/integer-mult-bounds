// Shared arithmetic for entries 14 to 16 (8 October 2026, later): rounded log bounds,
// a role budget for a batched bit moment, the "every complex residual" moment and the
// rho = 3/2 path guard used by PR 15 (eumemic) and PR 16 (jacklightChen).
//
// Top-down. PRs 14 to 16 keep PR 10's mixed-width recurrence and change only the child
// list: which rank units are compiled as one wide child instead of singletons.
//  - Bit network: more contiguous pivot blocks (PR 13's source-frame exit, the data
//    corners of PR 14 and PR 16, PR 16's diagonal exit corner). Each block is a child of
//    width t; the rest stay singletons, S = s - sum copies * t. The finite claim is
//    Psi(1 - a_b) = sum w_i r_i^(-a_b) < 1 (batched.ts).
//  - Complex network (PRs 15, 16): every nonzero physical edge of rank r becomes one
//    child of width r. The moment is sum_r (H_r r/(W m)) (m/r)^(a_c) < 1, where H_r is the
//    global histogram of edge ranks; the rank sum must equal s. The precision guard then
//    needs a path moment for any list of child ranks with total at most q = m + 6h and
//    parts at most M = m - 2h: by convexity (M/m)^rho + ((q - M)/m)^rho < 999/1000 at
//    rho = 3/2, giving C1 = rho - (rho - 1) beta + zeta = 3/2 - beta/2 + zeta.

import { type Q, q, add, sub, mul, div, lt, le, ONE, ZERO, pow } from "../rational";
import { floorRoot } from "../intmath";
import { logInverseEnclosure, momentWeights, momentUpperSecond, type WidthClass } from "./batched";

/** This checker's upper enclosure of log(1/r), rounded up to a multiple of 1/grid. */
export function roundedLogUp(r: Q, grid: bigint): Q {
  const u = logInverseEnclosure(r).upper;
  return q((u.num * grid + u.den - 1n) / u.den, grid);
}

/** Largest R (by bisection) for which `classesOf(R)` still gives momentUpperSecond(a) < 1. */
export function roleBudget(R0: bigint, a: Q, build: (R: bigint) => { m: bigint; W: bigint; s: bigint; classes: WidthClass[] }) {
  const ok = (R: bigint) => {
    const n = build(R);
    const b = momentUpperSecond(momentWeights(n.m, n.W, n.s, n.classes).items, a).bound;
    return lt(b, ONE);
  };
  if (!ok(R0)) return R0 - 1n;
  let lo = R0;
  let hi = R0 * 2n;
  while (ok(hi)) hi *= 2n;
  while (hi - lo > 1n) {
    const mid = (lo + hi) / 2n;
    if (ok(mid)) lo = mid;
    else hi = mid;
  }
  return lo;
}

/** Largest k with momentUpperBound(k/unit, ells) < 1 (the notes' conservative comparison with fixed log bounds). */
export function largestGridConservative(items: { w: Q }[], ells: Q[], unit: bigint, start: bigint) {
  const bound = (k: bigint) => {
    let s = ZERO;
    items.forEach((it, i) => {
      const x = mul(q(k, unit), ells[i]!);
      s = lt(x, ONE) ? add(s, div(it.w, sub(ONE, x))) : q(10n);
    });
    return s;
  };
  let k = start;
  if (!lt(bound(k), ONE)) {
    while (k > 0n && !lt(bound(k), ONE)) k--;
    return k;
  }
  while (lt(bound(k + 1n), ONE)) k++;
  return k;
}

// ------------------------------------------------------------------ complex histograms

/** Width classes for a histogram of edge ranks: rank 1 stays the singleton class; every rank r >= 2 is one child of width r. */
export function histogramClasses(hist: Map<bigint, bigint>): WidthClass[] {
  return [...hist.entries()].filter(([r]) => r >= 2n).sort((x, y) => (x[0] < y[0] ? -1 : 1)).map(([r, c]) => ({ name: `rank ${r}`, copies: c, t: r }));
}

export const histogramRankSum = (hist: Map<bigint, bigint>) => [...hist.entries()].reduce((acc, [r, c]) => acc + r * c, 0n);

// ------------------------------------------------------------------ the rho = 3/2 path guard

/** (1 - t)^(3/2) <= 1 - 3t/2 + (3/8) t^2/(1 - t): PR 16's Taylor bound (second derivative bounded on [0, t]). */
export const taylorThreeHalves = (t: Q) => add(sub(ONE, mul(q(3n, 2n), t)), div(mul(q(3n, 8n), mul(t, t)), sub(ONE, t)));

/** x^(3/2) <= U  <=>  x^3 <= U^2 (x, U >= 0): exact. */
export const threeHalvesBelow = (x: Q, U: Q) => U.num >= 0n && le(pow(x, 3), pow(U, 2));

/** Upper bound of x^(3/2) = x sqrt(x) with sqrt rounded up on the grid 1/D. */
export function threeHalvesUpper(x: Q, D: bigint): Q {
  // sqrt(x) <= ceil(sqrt(x D^2)) / D; x D^2 = num D^2 / den, so sqrt <= (floorRoot(num D^2 den) + 1)/(den D)
  const s = floorRoot(x.num * D * D * x.den, 2) + 1n;
  return mul(x, q(s, x.den * D));
}

/**
 * The convex path-moment bound at rho = 3/2 (complex-all-residuals.md, nested-complex.tex):
 * any list of ranks r_e <= M with sum <= q has sum (r_e/m)^(3/2) <= (M/m)^(3/2) + ((q - M)/m)^(3/2)
 * when M < q < 2M (moving mass into the largest part increases a convex sum).
 */
export function convexPathBound(m: bigint, h: bigint, M: bigint) {
  const qq = m + 6n * h;
  const shape = M < qq && qq < 2n * M;
  const t = q(m - M, m);
  const y = q(qq - M, m);
  const T = taylorThreeHalves(t);
  const taylorValid = threeHalvesBelow(q(M, m), T); // (1-t)^(3/2) <= T
  const yNineValid = threeHalvesBelow(y, div(y, q(9n))); // y^(3/2) <= y/9  <=>  y <= 1/81
  const pr16Bound = add(T, div(y, q(9n)));
  const sharp = add(threeHalvesUpper(q(M, m), 10n ** 20n), threeHalvesUpper(y, 10n ** 20n));
  return { qq, shape, t, y, T, taylorValid, yNineValid, pr16Bound, sharp };
}

/** Constants of the rho guard: E = 64(W+m+1)^3, C_dep = 1000(E + 16m + 1), C1 = rho - (rho-1) beta + zeta, C0 = ceil(128 m (1 + 1/zeta) C_dep). */
export function rhoGuardConstants(W: bigint, m: bigint, rho: Q, beta: Q, zeta: Q) {
  const E = 64n * (W + m + 1n) ** 3n;
  const Cdep = 1000n * (E + 16n * m + 1n);
  const C1 = add(sub(rho, mul(sub(rho, ONE), beta)), zeta);
  const raw = mul(q(128n * m * Cdep), add(ONE, div(ONE, zeta)));
  const C0 = (raw.num + raw.den - 1n) / raw.den;
  return { E, Cdep, C1, C0 };
}
