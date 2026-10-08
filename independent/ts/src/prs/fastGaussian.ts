// PR 5 (eumemic): fast Gaussian resampling. Sources at prs/5 (head d3d370c, base
// 6e56487, contains PR 3): notes/fast-gaussian-note.tex,
// notes/fast-gaussian-resampling.tex, patches/fast-gaussian-30.patch (hunks for
// 07-resampling.tex and 08-assembly.tex), read against PR 3's
// patches/complex-circuit-31.patch to see what changed.
//
// What changes in the parameter system (08-assembly, relative to PR 3):
//   - cost row "Gaussian line maps": d p^{1/2+delta} alpha, power 3/4 + delta + 5eps/4
//     becomes d^2 p^delta, power 2 eps + delta; so g5 = 1/4 - delta - 5eps/4 becomes
//     g5 = 1 - delta - 2 eps;
//   - the "remaining comparisons" drop eps < 1/3 and 3/4 + delta + 5eps/4 < 1 and
//     add 2 eps + delta < 1;
//   - alpha = ceil((32db)^{1/4}) becomes alpha = floor(sqrt(b/(8d))), so the size
//     conditions "alpha exponent < 1/2" and "gamma exponent < 1" are replaced by
//     gamma <= b/4 and alpha^2 < p, which hold for every b and d (identities);
//   - new eventual conditions: b >= 96d (alpha >= 2, alpha^2 >= b/(16d)) and
//     b >= 64 d^2 (alpha^2 theta_i >= 1), the latter needing 2 eps < 1.
// Everything else (layer conditions, guard, margins g1..g4, g6, g7) is unchanged.
//
// What the new lemmas add (07-resampling, sec:fast-gaussian): finite constants and
// algebraic identities, listed in `lemmaRows`, and analytic statements that are
// not finite arithmetic (listed in ANALYTIC, reported, never counted).

import { type Q, q, add, sub, mul, div, lt, le, ONE, ZERO, show, toDecimal } from "../rational";
import { compactParameterChecks, type CompactParams } from "../compact/witness";
import { margins as assemblyMargins, type Check } from "../parameters";
import { logEnclosureNearOne, expLowerBound } from "../log";
import { floorRoot } from "../intmath";
import { truth, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
export const FG_NOTE = "PR5 fast-gaussian-note.tex";
export const FG_RES = "PR5 fast-gaussian-resampling.tex";
export const FG_PATCH = "PR5 fast-gaussian-30.patch 08-assembly";

/** The seven margins with the new Gaussian row (patch eq:margin-list). */
export function fastMargins(p: CompactParams) {
  return { ...assemblyMargins(p), g5: sub(sub(ONE, p.delta), mul(q(2n), p.epsilon)) };
}
export const fastMinimumMargin = (p: CompactParams) => Object.values(fastMargins(p)).reduce((m, x) => (lt(x, m) ? x : m));

/** Conditions of the compact system that PR 5 removes (they fail at its eps; see the observation rows). */
export const DROPPED = ["epsilon < 1/3", "3/4 + delta + 5*epsilon/4 < 1", "alpha exponent 1/4+epsilon/4 < 1/2", "gamma exponent 1/2+3*epsilon/2 < 1"];

/** Every stated inequality on the fixed parameters, as patched by PR 5. */
export function fastParameterChecks(p: CompactParams): Check[] {
  const kept = compactParameterChecks(p).filter((k) => !DROPPED.includes(k.name));
  return [
    ...kept,
    { name: "2*epsilon + delta < 1", source: FG_PATCH + " remaining comparisons (g5 > 0, Gaussian line maps)", lhs: add(mul(q(2n), p.epsilon), p.delta), rel: "<", rhs: ONE, kind: "condition" },
    {
      name: "1 - 2 epsilon > 0 (b/d^2 grows, so alpha^2 theta_i >= 1 eventually)",
      source: FG_PATCH + " (same inequality as 2*epsilon < 1)",
      lhs: ZERO,
      rel: "<",
      rhs: sub(ONE, mul(q(2n), p.epsilon)),
      kind: "implied",
    },
  ];
}

/** The guard threshold: eps C1 < 1 with C1 = 5 - 4 beta + zeta  <=>  beta > (5 + zeta - 1/eps)/4. */
export const guardBetaThreshold = (p: CompactParams) => div(sub(add(q(5n), p.zeta), div(ONE, p.epsilon)), q(4n));

/**
 * The note: "with the original complex saving 418/10^12 no beta satisfies both" (guard and leaf),
 * at this eps and kappa. Leaf with g3 > kappa needs (1 - beta) a_c > 1 - lambda' > kappa/eps; the guard
 * needs beta > threshold. Both together need (1 - threshold) a_c > kappa/eps.
 */
export function leafAndGuardCompatible(p: CompactParams, ac: Q): boolean {
  return lt(div(p.kappa, p.epsilon), mul(sub(ONE, guardBetaThreshold(p)), ac));
}

// ---------------------------------------------------------------- constants

/** atan(x) for 0 < x < 1 by the alternating series: [S_K, S_{K+1}] in some order. */
function atanEnclosure(x: Q, K: number) {
  let s = ZERO;
  let pw = x;
  let prev = ZERO;
  for (let k = 0; k <= K; k++) {
    prev = s;
    const term = div(pw, q(BigInt(2 * k + 1)));
    s = k % 2 === 0 ? add(s, term) : sub(s, term);
    pw = mul(pw, mul(x, x));
  }
  return lt(prev, s) ? { lower: prev, upper: s } : { lower: s, upper: prev };
}

/** pi = 16 atan(1/5) - 4 atan(1/239) (Machin), with rigorous bounds. */
export function piEnclosure(K = 30) {
  const a = atanEnclosure(q(1n, 5n), K);
  const b = atanEnclosure(q(1n, 239n), K);
  return { lower: sub(mul(q(16n), a.lower), mul(q(4n), b.upper)), upper: sub(mul(q(16n), a.upper), mul(q(4n), b.lower)) };
}
export const PI = piEnclosure();
export const LN2 = logEnclosureNearOne(q(2n), 40);

/** Analytic statements of PR 5 that are not finite arithmetic (reported, not counted). */
export const ANALYTIC = [
  "Harvey and van der Hoeven Theorem 4.2 and Lemmas 2.13, 2.14, 4.5 to 4.12 (cited, upstream), and the claims that Lemma 4.6 needs only alpha^2 theta >= 1 and Proposition 4.7(i) only ||N - I|| < 0.42, alpha >= 2 and Lemma 4.5",
  "the path expansion (E^n u)_l = sum over paths, the formula for E and X_{l,h} >= 0 in general, and the passage from X >= sigma sum h_i^2 - 1/(4 theta) - 1/2 to the operator-norm bound on ||E^n||",
  "the Neumann evaluation of Lemma 4.12 run with ||E^n|| <= 2^-p in place of ||E||^n (error 3p^2/4 unchanged)",
  "exactness of the packed correlation (no slot overflow with 2P + ceil(log2(F L_A)) + 8 bits) and the cost of the established multiplier",
  "tape movement: periodic copies, block offsets, O((t + p) p^(1+delta)) per line, and the tensor sum O(d T p^(1+delta)(1 + n_*))",
  "prime selection eta < theta_i < 1/(2d - 1), t_i >= r/2 > p, and the eventual conditions b >= 96d and b >= 64 d^2 (true for large n; only their exponent arithmetic and instances are checked)",
  "completeness of the cost table: that the Gaussian row is the only row that changes",
];

const ge = (a: Q, b: Q) => le(b, a);

/** Rows for the finite parts of the new lemmas. `p` supplies nothing here: they do not depend on the witness. */
export function lemmaRows(section: string): Result[] {
  const out: Result[] = [];
  const C = (name: string, src: string, ok: boolean, detail = "") => out.push(truth(section, name, src, ok, detail, "constant"));
  const I = (name: string, src: string, ok: boolean, detail = "") => out.push(truth(section, name, src, ok, detail, "identity"));
  const S = (name: string, src: string, ok: boolean, detail = "") => out.push(truth(section, name, src, ok, detail, "sample"));
  const pi = PI;
  const kappa0 = { lower: div(pi.lower, LN2.upper), upper: div(pi.upper, LN2.lower) };
  C("pi enclosure (Machin) lies in (3.14159265358, 3.14159265359)", "used by every constant below", lt(q(314159265358n, TEN(11)), pi.lower) && lt(pi.upper, q(314159265359n, TEN(11))));
  // Corollary cor:neumann-count
  C("kappa_0 = pi log2 e = pi / ln 2 lies in (4.531, 4.534)", FG_RES + " cor:neumann-count", lt(q(4531n, 1000n), kappa0.lower) && lt(kappa0.upper, q(4534n, 1000n)), `[${toDecimal(kappa0.lower, 8)}, ${toDecimal(kappa0.upper, 8)}]`);
  C("log2 2.01 < 1.01, i.e. 201^100 < 2^101 * 100^100", FG_RES + " cor:neumann-count", 201n ** 100n < 2n ** 101n * 100n ** 100n);
  C("4.531 * 4 - 1.01 >= 4 * 4 and 4.531 >= 4 (so kappa_0 alpha^2 sigma - 1.01 >= 4 alpha^2 for alpha >= 2, sigma > 1)", FG_RES + " cor:neumann-count", ge(sub(mul(q(4531n, 1000n), q(4n)), q(101n, 100n)), q(16n)));
  C("4.534 (1/(4 theta) + 1/2) <= 4/theta for 0 < theta < 1: 4.534/4 + 4.534/2 <= 4", FG_RES + " cor:neumann-count", le(add(div(q(4534n, 1000n), q(4n)), div(q(4534n, 1000n), q(2n))), q(4n)));
  // eq:gaussian-public-facts
  const halfPiLow = div(pi.lower, q(2n));
  const eHalfPi = expLowerBound(halfPiLow, 40);
  C("2.01 e^(-pi/2) < 0.42, i.e. e^(pi/2) > 201/42", FG_NOTE + " lem:no-sort-resampling proof", lt(q(201n, 42n), eHalfPi));
  C("pi/2 > ln 2 (so 2.01 e^(-pi x/2) 2^x decreases in x)", FG_NOTE + " eq:gaussian-public-facts", lt(LN2.upper, halfPiLow));
  out.push(truth(section, "2.01 e^(-pi x/2) < 2^(-x) for all x >= 1 (at x = 1: e^(pi/2) > 4.02; implied by the two rows above)", FG_NOTE + " eq:gaussian-public-facts", lt(q(402n, 100n), eHalfPi), "", "implied"));
  C("0.42 < 1/2 (||E|| < 1/2 for the Neumann series)", FG_NOTE, lt(q(42n, 100n), q(1n, 2n)));
  // lem:correction-powers, the inner sum
  C("pi alpha^2 sigma > 4 pi > 12 for alpha >= 2, sigma > 1 (pi > 3)", FG_RES + " lem:correction-powers", lt(q(3n), pi.lower));
  C("e^(3A) > 2^36 > 400 for A > 12, so 2(1 + 2 e^(-3A)) <= 2 (1 + 1/200) = 2.01", FG_RES + " lem:correction-powers", 2n ** 36n > 400n && le(mul(q(2n), add(ONE, q(2n, 400n))), q(201n, 100n)));
  C("tail: e^(-8A) + e^(-15A) + ... <= e^(-3A) when e^(-5A) <= 1/2 (A > 12, 2^60 > 2)", FG_RES + " lem:correction-powers", 2n ** 60n > 2n);
  I("sigma/(4 theta) + 1/4 = 1/(4 theta) + 1/2 when sigma = 1 + theta (theta = 1/7, 1/31, 5/251)", FG_RES, [q(1n, 7n), q(1n, 31n), q(5n, 251n)].every((t) => {
    const s = add(ONE, t);
    return eq_(add(div(s, mul(q(4n), t)), q(1n, 4n)), add(div(ONE, mul(q(4n), t)), q(1n, 2n)));
  }));
  // lem:chirped-gaussian
  C("S': (pi/4)(1.21) / ln 2 <= 1.4, so Gamma = ceil(1.4 p) bits suffice", FG_RES + " lem:chirped-gaussian (map S')", le(div(mul(div(pi.upper, q(4n)), q(121n, 100n)), LN2.lower), q(14n, 10n)));
  C("E: pi / (4 ln 2) < 1.14, so F = e^(pi alpha^2/4) < 2^(1.14 alpha^2)", FG_RES + " lem:chirped-gaussian (map E)", lt(div(pi.upper, mul(q(4n), LN2.lower)), q(114n, 100n)));
  C("E: (25 pi/4) / ln 2 <= 29, so Gamma = ceil(29 p) bits suffice", FG_RES + " lem:chirped-gaussian (map E)", le(div(mul(q(25n, 4n), pi.upper), LN2.lower), q(29n)));
  C("one block: 2^5 + 2^1 + 2^5 <= 2^7 (rounded g_a, K_r and their product into 2^(7-P) F per term, P >= 1)", FG_RES + " one block", 32 + 2 + 32 <= 128);
  C("one block: 2^7 + 2^1 + 2^7 <= 2^9 (correlation error and factor error into 2^(Gamma+9-P) F L_A)", FG_RES + " one block", 128 + 2 + 128 <= 512);
  C("errors: 1 + 1/4 + 1 < 3 (S') and 3 + 1 + 1 < p/3 for p > 15 (E)", FG_RES, lt(q(9n, 4n), q(3n)) && lt(q(5n), q(16n, 3n)));
  // P budgets for every p in a range (Gamma <= 2P too)
  const isqrtCeil = (x: bigint) => {
    const r = floorRoot(x, 2);
    return r * r === x ? r : r + 1n;
  };
  const ceilLog2 = (x: bigint) => (x <= 1n ? 0n : BigInt((x - 1n).toString(2).length));
  let okS = true;
  let okE = true;
  let worst = "";
  for (let p = 101n; p <= 20000n; p++) {
    // S': m = ceil(sqrt p) alpha with alpha < sqrt p, so alpha <= ceil(sqrt p) - 1; F = 1
    const r = isqrtCeil(p);
    const mS = r * (r - 1n);
    const GammaS = (14n * p + 9n) / 10n;
    if (!(p + GammaS + ceilLog2(3n * mS + 3n) + 11n <= 3n * p && GammaS <= 6n * p)) {
      okS = false;
      worst = `S' fails at p = ${p}`;
    }
    // E: m = ceil(sqrt p / (2 alpha)) <= ceil(sqrt p / 4) with alpha >= 2; log2 F <= 1.14 p
    const mE = (r + 3n) / 4n;
    const logF = (114n * p + 99n) / 100n;
    if (!(p + 29n * p + logF + ceilLog2(3n * mE + 1n) + 11n <= 34n * p && 29n * p <= 68n * p)) {
      okE = false;
      worst = `E fails at p = ${p}`;
    }
  }
  S("precision budgets: p + Gamma + ceil(log2(F L_A)) + 11 <= P (P = 3p for S', 34p for E) and Gamma <= 2P, every p = 101..20000", FG_RES + " lem:chirped-gaussian", okS && okE, worst);
  // windows: S' and E blocks contain the required indices (finite, on samples)
  S("block windows: S' inputs cover |j - k/sigma| < m, E evaluation points cover q_l, E inputs cover |h| <= m (samples)", FG_RES + " lem:chirped-gaussian", windowSamples(), "");
  // chirp identity, exactly as a polynomial identity on samples
  I("chirp identity (sigma a^ - b)^2 = sigma theta a^2 + sigma (a^ - b)^2 - theta b^2 with sigma = 1 + theta (random rationals)", FG_RES + " eq:chirp-split", chirpSamples());
  // step identity and inequality, exhaustively on sample (s, t)
  const steps = stepSamples();
  S("step identity c(j,h) - Phi(j+h) + Phi(j) = sigma h^2 + (sigma/theta) w (2y - w), excess >= 0, X_{l,h} >= 0 (all j mod s, 0 < |h| <= 3s, five (s,t))", FG_RES + " lem:correction-powers", steps.ok, steps.detail);
  S("path bound X >= sigma sum h_i^2 - 1/(4 theta) - 1/2 on 2000 random paths per (s,t)", FG_RES + " lem:correction-powers", steps.paths);
  return out;
}

const eq_ = (a: Q, b: Q) => a.num === b.num && a.den === b.den;

/** The five (s, t) of the certificate's step samples (keys s/t), plus two more. */
export const STEP_SAMPLES: [number, number][] = [
  [251, 256],
  [31, 32],
  [61, 64],
  [7, 8],
  [97, 101],
];

function qj(s: number, t: number, j: number): { q: bigint; beta: Q } {
  // q_j = floor(t j / s + 1/2), beta_j = t j / s - q_j
  const num = BigInt(2 * t * j + s);
  const den = BigInt(2 * s);
  const fl = num >= 0n ? num / den : -((-num + den - 1n) / den);
  return { q: fl, beta: sub(q(BigInt(t * j), BigInt(s)), q(fl)) };
}

/** Exact step quantities for every j in [0, s) and 0 < |h| <= H. Returns the minimum excess per (s,t). */
export function stepExcess(s: number, t: number, H: number) {
  const sigma = q(BigInt(t), BigInt(s));
  const theta = sub(sigma, ONE);
  const Phi = (b: Q) => div(mul(sigma, add(mul(b, b), q(1n, 4n))), theta);
  let min: Q | null = null;
  let identity = true;
  let nonneg = true;
  for (let j = 0; j < s; j++) {
    const a = qj(s, t, j);
    for (let h = -H; h <= H; h++) {
      if (h === 0) continue;
      const b = qj(s, t, j + h);
      const H_ = q(BigInt(h));
      const c = mul(mul(sigma, H_), add(mul(sigma, H_), mul(q(2n), a.beta))); // sigma h (sigma h + 2 beta_j)
      const X = sub(mul(add(mul(sigma, H_), a.beta), add(mul(sigma, H_), a.beta)), mul(b.beta, b.beta));
      if (lt(X, ZERO)) nonneg = false;
      const excess = sub(sub(sub(c, Phi(b.beta)), mul(q(-1n), Phi(a.beta))), mul(sigma, mul(H_, H_)));
      const y = add(a.beta, mul(H_, theta));
      const w = q(b.q - a.q - BigInt(h));
      const closed = mul(div(sigma, theta), mul(w, sub(mul(q(2n), y), w)));
      if (!eq_(excess, closed)) identity = false;
      if (min === null || lt(excess, min)) min = excess;
    }
  }
  return { min: min!, identity, nonneg };
}

function stepSamples() {
  let ok = true;
  const mins: string[] = [];
  for (const [s, t] of STEP_SAMPLES) {
    const r = stepExcess(s, t, Math.min(3 * s, 120));
    if (!(r.identity && r.nonneg && le(ZERO, r.min))) ok = false;
    mins.push(`${s}/${t}: min ${show(r.min)}`);
  }
  // random paths
  let paths = true;
  let seed = 12345;
  const rnd = () => ((seed = (seed * 1103515245 + 12345) % 2147483648), seed / 2147483648);
  for (const [s, t] of STEP_SAMPLES) {
    const sigma = q(BigInt(t), BigInt(s));
    const theta = sub(sigma, ONE);
    for (let k = 0; k < 2000; k++) {
      let j = Math.floor(rnd() * s);
      const len = 1 + Math.floor(rnd() * 6);
      let X = ZERO;
      let sh2 = ZERO;
      for (let i = 0; i < len; i++) {
        let h = 0;
        while (h === 0) h = Math.floor(rnd() * 13) - 6;
        const a = qj(s, t, j);
        const b = qj(s, t, j + h);
        const H_ = q(BigInt(h));
        X = add(X, sub(mul(add(mul(sigma, H_), a.beta), add(mul(sigma, H_), a.beta)), mul(b.beta, b.beta)));
        sh2 = add(sh2, mul(H_, H_));
        j += h;
      }
      if (lt(X, sub(sub(mul(sigma, sh2), div(ONE, mul(q(4n), theta))), q(1n, 2n)))) paths = false;
    }
  }
  return { ok, detail: mins.join("; "), paths };
}

function chirpSamples(): boolean {
  let seed = 7;
  const r = (k: number) => ((seed = (seed * 48271) % 2147483647), BigInt((seed % (2 * k + 1)) - k));
  const abs = (x: bigint) => (x < 0n ? -x : x);
  for (let i = 0; i < 200; i++) {
    const theta = q(1n + abs(r(50)), 7n + abs(r(40)));
    const sigma = add(ONE, theta);
    const a = q(r(1000), 1n + abs(r(30)));
    const b = q(r(1000));
    const lhs = mul(sub(mul(sigma, a), b), sub(mul(sigma, a), b));
    const rhs = sub(add(mul(mul(sigma, theta), mul(a, a)), mul(sigma, mul(sub(a, b), sub(a, b)))), mul(theta, mul(b, b)));
    if (!eq_(lhs, rhs)) return false;
  }
  return true;
}

function windowSamples(): boolean {
  for (const [s, t] of STEP_SAMPLES) {
    const sigma = q(BigInt(t), BigInt(s));
    for (const m of [1, 2, 3, 5, 8]) {
      // S': block k0..k0+m-1, inputs j0..j0+3m+2, j0 = floor(k0/sigma) - m
      for (let k0 = 0; k0 < t; k0 += 7) {
        const k0s = div(q(BigInt(k0)), sigma);
        const j0 = Number(k0s.num / k0s.den) - m;
        for (let k = k0; k < k0 + m; k++) {
          const ks = div(q(BigInt(k)), sigma);
          for (let j = j0 - 3 * m - 5; j <= j0 + 6 * m + 5; j++) {
            const d = sub(q(BigInt(j)), ks);
            const inside = lt(d.num < 0n ? q(-d.num, d.den) : d, q(BigInt(m)));
            if (inside && !(j >= j0 && j <= j0 + 3 * m + 2)) return false;
          }
        }
      }
      // E: block l0..l0+m-1; evaluation points q_{l0} + b', 0 <= b' < 2m + 2; inputs l0 - m .. l0 + 2m
      for (let l0 = 0; l0 < s; l0 += 5) {
        const q0 = qj(s, t, l0).q;
        for (let l = l0; l < l0 + m; l++) {
          const off = qj(s, t, l).q - q0;
          if (!(off >= 0n && off < BigInt(2 * m + 2))) return false;
          for (let h = -m; h <= m; h++) if (!(l + h >= l0 - m && l + h <= l0 + 2 * m)) return false;
        }
      }
    }
  }
  return true;
}

/**
 * Parameter-level facts of the new Gaussian width for one pair (b, d), d >= 3:
 * alpha = floor(sqrt(b/(8d))), gamma = 2 d alpha^2, p = 6b, theta in (1/(4d), 1/(2d-1)).
 */
/** floor(sqrt(n)) by integer Newton iteration (exact; floorRoot's bisection is too slow at 10^5 bits). */
export function isqrt(n: bigint): bigint {
  if (n < 0n) throw new Error("isqrt of a negative number");
  if (n < 2n) return n;
  let x = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
  for (;;) {
    const y = (x + n / x) >> 1n;
    if (y >= x) return x;
    x = y;
  }
}

export function fastWidthInstance(b: bigint, d: bigint) {
  const alpha = isqrt(b / (8n * d)); // floor(sqrt(floor(b/(8d)))) = floor(sqrt(b/(8d)))
  const a2 = alpha * alpha;
  const p = 6n * b;
  const gamma = 2n * d * a2;
  // Neumann count bound with 1/theta < 4d: ceil((p+1)/(4 alpha^2) + 4d) (an upper bound for every admissible theta)
  const nNum = p + 1n + 16n * d * a2;
  const nDen = 4n * a2;
  const nMax = (nNum + nDen - 1n) / nDen;
  // the classical count at theta = 1/(4d): ceil(p / (alpha^2 theta)) = ceil(4 d p / alpha^2)
  const nHvdh = (4n * d * p + a2 - 1n) / a2;
  return {
    alpha,
    gamma,
    nMax,
    nHvdh,
    facts: {
      bAtLeast96d: b >= 96n * d,
      bAtLeast64d2: b >= 64n * d * d,
      dAtLeast3: d >= 3n,
      alphaAtLeast2: alpha >= 2n,
      alphaSqAtLeastBover16d: 16n * d * a2 >= b,
      alphaSqBelowP: a2 < p,
      gammaAtMostBover4: 4n * gamma <= b,
      alphaSqThetaAtLeast1: a2 >= 4n * d, // alpha^2 / (4d) >= 1, and theta > 1/(4d)
      neumannAtMost30d: nMax <= 30n * d,
      neumannAtMostP: nMax <= p,
    },
  };
}

/** b = 2^k with k a multiple of 10^5 makes d = floor(b^eps) = 2^(k eps) exact for eps = u/10^5. */
export function exactPowerInstance(k: number, epsilon: Q) {
  const ke = q(BigInt(k) * epsilon.num, epsilon.den);
  if (ke.den !== 1n) throw new Error("k eps must be an integer");
  const b = 1n << BigInt(k);
  const d = 1n << ke.num;
  return { k, b, d, ...fastWidthInstance(b, d) };
}

/** Exponent of b beyond which b >= 64 d^2 holds for d = floor(b^eps): b^(1-2eps) >= 64. */
export const cutoff64d2 = (epsilon: Q) => div(q(6n), sub(ONE, mul(q(2n), epsilon)));
/** b^(1-eps) >= 96 holds once b >= 2^(7/(1-eps)), since 96 < 2^7. */
export const cutoff96d = (epsilon: Q) => div(q(7n), sub(ONE, epsilon));
