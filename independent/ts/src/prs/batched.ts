// Shared arithmetic for the batched recursions of PR 10 (icekylinx) and the PRs that
// build on it (PR 12, PR 13). Written from the notes of prs/10 (62691e3):
// notes/projector-batching.tex, notes/batched-bit-rank-accounting.tex,
// notes/controlled-projector-basis.tex, notes/batched-bit-rows.tex,
// notes/bulk-complex-guard.tex, notes/batched-complex-rows.tex,
// notes/batched-assembly.tex and the 08-assembly hunk of patches/batched-23.patch.
//
// Top-down: what batching changes.
//   Before: an edge of rank a is compiled as a recursive calls of width e/m, so a
//   network with rank sum s and W roles has the uniform moment s/(W m^tau), and the
//   saving is the a with s/W = m^(1-a), i.e. a = -log(1 - eta)/log m.
//   After: a selected edge may be compiled with fewer, wider children (a child of
//   width t e/m for an integer 1 <= t <= m - 1). The rank sum is unchanged (the
//   widths of one edge add up to its rank), so the moment at exponent 1 is still
//   s/(W m) = 1 - eta. But at exponent tau < 1 a wide child costs (t/m)^tau, much less
//   than t (1/m)^tau. The new recurrence moment is
//       Psi(tau) = (1/W) [ S m^(-tau) + sum_classes copies (t/m)^tau ],
//       S = s - sum_classes copies * t      (the remaining singleton calls),
//   and the claimed saving is any a with Psi(1 - a) < 1 (an analytic recurrence lemma
//   turns this into F(e) = O(e^(1-a)); the lemma is NOT finite arithmetic).
//   Writing r = t/m and w = copies * t /(W m) (rank-mass weight), Psi(1 - a) =
//   sum w r^(-a) = sum w exp(a log(1/r)) <= sum w / (1 - a l) for upper bounds
//   l >= log(1/r) with a l < 1 (e^x <= 1/(1-x)). That last finite inequality is
//   what the notes certify, and what is recomputed here.
//
// Bit network (interchange): a projector edge of rank a > m/2 becomes (m - a)
// singleton pivots plus one contiguous block of width 2a - m; with the controlled
// basis the stage-two sink (nullity H = h^2) becomes one block of width H plus one
// of width m - 2H. Complex network: a selected residual of rank a is one child of
// width a ("whole residual"). Both are encoded as lists of width classes.

import { type Q, q, add, sub, mul, div, lt, le, ONE, ZERO, pow } from "../rational";
import { logIntegerEnclosure, logEnclosureNearOne, type Enclosure } from "../log";

/** One kind of child call: `copies` calls of width `t` (in units of e/m). */
export type WidthClass = { name: string; copies: bigint; t: bigint };

/** Remaining singleton calls and the rank-mass weights (r, w) of every child kind. */
export function momentWeights(m: bigint, W: bigint, s: bigint, classes: WidthClass[]) {
  let S = s;
  for (const c of classes) S -= c.copies * c.t;
  const Wm = W * m;
  const items = [{ name: "singleton", r: q(1n, m), w: q(S, Wm), t: 1n, copies: S }, ...classes.map((c) => ({ name: c.name, r: q(c.t, m), w: q(c.copies * c.t, Wm), t: c.t, copies: c.copies }))];
  const total = items.reduce((acc, x) => add(acc, x.w), ZERO);
  return { S, items, total };
}

/** Enclosure of log(1/r) for a rational 0 < r <= 1 (atanh series; for 1/r > 2 the power of two is extracted). */
export function logInverseEnclosure(r: Q, terms = 24): Enclosure {
  const x = div(ONE, r); // >= 1
  if (le(x, q(2n))) return logEnclosureNearOne(x, terms);
  // log(a/b) = log a - log b for integers
  const A = logIntegerEnclosure(x.num, terms);
  const B = x.den === 1n ? { lower: ZERO, upper: ZERO } : logIntegerEnclosure(x.den, terms);
  return { lower: sub(A.lower, B.upper), upper: sub(A.upper, B.lower) };
}

/** The notes' certified bound sum w_i / (1 - a l_i) with stated upper bounds l_i (one per item). */
export function momentUpperBound(items: { w: Q }[], a: Q, ells: Q[]) {
  if (ells.length !== items.length) throw new Error("one logarithm bound per child kind");
  let s = ZERO;
  items.forEach((it, i) => {
    const x = mul(a, ells[i]!);
    if (!lt(x, ONE)) throw new Error("a l >= 1: the bound e^x <= 1/(1-x) does not apply");
    s = add(s, div(it.w, sub(ONE, x)));
  });
  return { bound: s, gap: sub(ONE, s) };
}

/**
 * Second route, independent of the stated l_i: an upper bound of Psi(1-a) from this
 * checker's own log enclosures and the sharper e^x <= 1 + x + x^2/(2(1 - x/3)) (0 <= x < 3;
 * the tail x^k/k! <= (x^2/2)(x/3)^(k-2)).
 */
export function momentUpperSecond(items: { r: Q; w: Q }[], a: Q) {
  let s = ZERO;
  for (const it of items) {
    const L = logInverseEnclosure(it.r).upper;
    const x = mul(a, L);
    const e = add(add(ONE, x), div(mul(x, x), mul(q(2n), sub(ONE, div(x, q(3n))))));
    s = add(s, mul(it.w, e));
  }
  return { bound: s, gap: sub(ONE, s) };
}

/** Lower bound of Psi(1-a) (e^x >= 1 + x), to show how close a grid value is to failing. */
export function momentLower(items: { r: Q; w: Q }[], a: Q) {
  let s = ZERO;
  for (const it of items) s = add(s, mul(it.w, add(ONE, mul(a, logInverseEnclosure(it.r).lower))));
  return s;
}

/** Largest k with momentUpperSecond(k / unit) < 1 (an observation: how much room the stated saving leaves). */
export function largestGridSaving(items: { r: Q; w: Q }[], unit: bigint, start: bigint) {
  let k = start;
  if (!lt(momentUpperSecond(items, q(k, unit)).bound, ONE)) return { k: k - 1n, firstFail: k };
  let step = 1n;
  while (lt(momentUpperSecond(items, q(k + step, unit)).bound, ONE)) {
    k += step;
    step *= 2n;
  }
  // now k passes, k + step fails: bisect
  let lo = k;
  let hi = k + step;
  while (hi - lo > 1n) {
    const mid = (lo + hi) / 2n;
    if (lt(momentUpperSecond(items, q(mid, unit)).bound, ONE)) lo = mid;
    else hi = mid;
  }
  // and the first value at which even the lower bound reaches 1 (a true failure)
  let f = hi;
  while (lt(momentLower(items, q(f, unit)), ONE)) f += 1n;
  return { k: lo, firstFail: f };
}

// ------------------------------------------------------------------ bit rank classes

/**
 * The three large projector classes of the retained ternary network
 * (batched-bit-rank-accounting.tex) at ground size h, m = h^3, H = h^2:
 *   stage 1-3 join:        copies v^2 R, rank m - 2h, nullity 2h
 *   stage 2 sink:          copies v^2 R, rank m - H,  nullity H
 *   stage 3 data entrance: copies 2v^3,  rank (H - 1)(h - 1)
 * and their batched child widths. `controlled` uses the controlled basis for the
 * sink (one block of width H plus one of width m - 2H, no singleton corner);
 * `sourceFrames` uses PR 13's exit (rank m - h: h singletons plus one block m - 2h)
 * instead of the sink and removes the stage-two entrance singletons (h^2 - h per role).
 */
export function bitClasses(h: bigint, v: bigint, R: bigint, mode: "three" | "controlled" | "sourceFrames") {
  const m = h ** 3n;
  const H = h * h;
  const B = v * v * R;
  const N2 = 2n * v ** 3n;
  const a1 = m - 2n * h;
  const a2 = m - H;
  const a3 = (H - 1n) * (h - 1n);
  const k = (a: bigint) => 2n * a - m; // contiguous middle block of a rank-a idempotent
  const join: WidthClass = { name: "stage 1-3 join block", copies: B, t: k(a1) };
  const entrance: WidthClass = { name: "stage 3 data entrance block", copies: N2, t: k(a3) };
  if (mode === "three") return { ranks: { a1, a2, a3 }, classes: [join, { name: "stage 2 sink block", copies: B, t: k(a2) }, entrance], singletonShift: 0n };
  if (mode === "controlled")
    return { ranks: { a1, a2, a3 }, classes: [join, { name: "stage 2 sink middle block", copies: B, t: m - 2n * H }, entrance, { name: "stage 2 sink corner block (width H)", copies: B, t: H }], singletonShift: 0n };
  const a4 = m - h;
  return { ranks: { a1, a2, a3, a4 }, classes: [join, entrance, { name: "stage 2 auxiliary exit block", copies: B, t: k(a4) }], singletonShift: 0n };
}

// ------------------------------------------------------------------ the bulk complex guard

/** (1 - t)^(6/5) <= 1 - (6/5) t + (3/25) t^2/(1 - t), the note's Taylor bound. */
export const taylorSixFifths = (t: Q) => add(sub(ONE, mul(q(6n, 5n), t)), div(mul(q(3n, 25n), mul(t, t)), sub(ONE, t)));

/**
 * The guard of bulk-complex-guard.tex for path budget qq = m + 6h and selected ranks a_i:
 *   max{ qq/m^rho, (qq - a_i)/m^rho + (a_i/m)^rho } < 999/1000, rho = 6/5,
 * certified with m^rho > 160000 (160000^5 < m^6) and the Taylor bound. Returns the
 * note's rational upper bounds, and checks (exactly, by fifth powers) that each Taylor
 * value really bounds (a_i/m)^(6/5) from above.
 */
export function bulkPathBounds(m: bigint, h: bigint, ranks: bigint[], mRhoLower = 160000n) {
  const qq = m + 6n * h;
  const lowerOk = mRhoLower ** 5n < m ** 6n;
  const first = q(qq, mRhoLower);
  const rows = ranks.map((a) => {
    const t = q(m - a, m);
    const T = taylorSixFifths(t);
    // (a/m)^(6/5) <= T  <=>  (a/m)^6 <= T^5 (T > 0)
    const taylorValid = T.num > 0n && le(pow(q(a, m), 6), pow(T, 5));
    return { a, bound: add(q(qq - a, mRhoLower), T), taylorValid, t };
  });
  const atMostOne = ranks.every((a, i) => ranks.every((b, j) => i === j || a + b > qq)) && ranks.every((a) => 2n * a > qq);
  return { qq, lowerOk, first, rows, atMostOne };
}

/** Constants of the bulk guard: E = 64(W+m+1)^3, C_dep = 1000(E + 16m + 1), C1 = rho - (rho-1)beta + zeta, C0. */
export function bulkGuardConstants(W: bigint, m: bigint, beta: Q, zeta: Q) {
  const E = 64n * (W + m + 1n) ** 3n;
  const Cdep = 1000n * (E + 16n * m + 1n);
  const rho = q(6n, 5n);
  const C1 = add(sub(rho, mul(sub(rho, ONE), beta)), zeta);
  const raw = mul(q(128n * m * Cdep), add(ONE, div(ONE, zeta)));
  const C0 = (raw.num + raw.den - 1n) / raw.den;
  return { E, Cdep, C1, C0, rho };
}

// ------------------------------------------------------------------ the 29-row slack table

/**
 * The "twenty-nine strict parameter slacks" of the batched assembly (08-assembly hunk of
 * batched-23.patch), in the table's order. `chi` and `leaf` are the layer exponents.
 */
export function slackTable(p: { tau: Q; sigma: Q; c: Q; epsilon: Q; beta: Q; lambda: Q; lambdaPrime: Q; C1: Q; delta: Q; kappa: Q }, chi: Q, leaf: Q): [string, Q][] {
  const e = p.epsilon;
  const one = ONE;
  const maxQ = (x: Q, y: Q) => (lt(x, y) ? y : x);
  return [
    ["tau", p.tau],
    ["1-tau", sub(one, p.tau)],
    ["sigma", p.sigma],
    ["1-sigma", sub(one, p.sigma)],
    ["c", p.c],
    ["epsilon", e],
    ["beta", p.beta],
    ["1-beta", sub(one, p.beta)],
    ["lambda-tau", sub(p.lambda, p.tau)],
    ["lambda-sigma", sub(p.lambda, p.sigma)],
    ["1-lambda", sub(one, p.lambda)],
    ["lambda-chi", sub(p.lambda, chi)],
    ["lambda'-lambda", sub(p.lambdaPrime, p.lambda)],
    ["lambda'-h_leaf", sub(p.lambdaPrime, leaf)],
    ["1-lambda'", sub(one, p.lambdaPrime)],
    ["1-epsilon C1", sub(one, mul(e, p.C1))],
    ["(1-epsilon)(1-tau)", mul(sub(one, e), sub(one, p.tau))],
    ["1-epsilon(1+c)", sub(one, mul(e, add(one, p.c)))],
    ["1-delta-epsilon", sub(sub(one, p.delta), e)],
    ["delta", p.delta],
    ["1/8-delta", sub(q(1n, 8n), p.delta)],
    ["1-2 epsilon (prime intervals)", sub(one, mul(q(2n), e))],
    ["1-epsilon(1+c) (K = o(ell))", sub(one, mul(e, add(one, p.c)))],
    ["epsilon c", mul(e, p.c)],
    ["1-epsilon", sub(one, e)],
    ["kappa", p.kappa],
    ["1-delta-2 epsilon", sub(sub(one, p.delta), mul(q(2n), e))],
    ["1-2 epsilon (alpha^2 theta)", sub(one, mul(q(2n), e))],
    ["lambda'-max{1-c,0}", sub(p.lambdaPrime, maxQ(sub(one, p.c), ZERO))],
  ];
}

/**
 * The corrected chirp precision budget (chirp-scaling-correction.tex): for integers p > 100 and
 * 2 <= alpha < sqrt p, with L_A = 3 ceil(sqrt p/(2 alpha)) + 1, Gamma = 29p, B = ceil(1.14 alpha^2),
 * F = 2^B: p + Gamma + ceil(log2(F L_A)) + 11 <= 34p (and the intermediate claims L_A <= p,
 * ceil(log2 L_A) <= p - 1, B <= 1.14p + 1). Exhaustive over a range of p and every alpha.
 */
export function chirpBudget(pMax: number) {
  const ceilLog2 = (x: bigint) => (x <= 1n ? 0n : BigInt((x - 1n).toString(2).length));
  const isqrt = (x: bigint) => {
    let r = BigInt(Math.floor(Math.sqrt(Number(x))));
    while (r * r > x) r--;
    while ((r + 1n) * (r + 1n) <= x) r++;
    return r;
  };
  let worst = 0n; // largest (lhs - 32p - 11) seen, must stay <= 0.14p
  let ok = true;
  let detail = "";
  for (let p = 101n; p <= BigInt(pMax); p++) {
    for (let alpha = 2n; alpha * alpha < p; alpha++) {
      // ceil(sqrt p / (2 alpha)) = smallest k with (2 alpha k)^2 >= p
      let k = isqrt(p) / (2n * alpha);
      while ((2n * alpha * k) ** 2n < p) k++;
      while (k > 0n && (2n * alpha * (k - 1n)) ** 2n >= p) k--;
      const LA = 3n * k + 1n;
      const B = (114n * alpha * alpha + 99n) / 100n;
      const lhs = p + 29n * p + B + ceilLog2(LA) + 11n;
      const bounds = LA <= p && ceilLog2(LA) <= p - 1n && 100n * B <= 114n * p + 100n && 100n * lhs <= 3214n * p + 1100n;
      if (!(lhs <= 34n * p) || !bounds) {
        ok = false;
        detail = `fails at p = ${p}, alpha = ${alpha}`;
      }
      if (lhs - 32n * p - 11n > worst) worst = lhs - 32n * p - 11n;
    }
  }
  return { ok, detail };
}
