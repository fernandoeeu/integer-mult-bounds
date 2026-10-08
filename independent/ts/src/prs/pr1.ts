// PR 1 (Aurel Prosz): "A near-optimal parameter-only refinement of the paired witness".
// Source: docs/paired-tuned-parameters.md at prs/1 (base bcd4ebd), and the patch
// patches/h50-paired-tuned.patch for the conditions it restates.
//
// Top-down: the bit and complex networks and their savings a = 296/10^11,
// b = a_c = 1/10^11 are unchanged (certified by B1, B2 of `bun run check` and by
// the unchanged h = 50 complex counts). Only the downstream parameters of the
// preserved 2^-59 witness change: beta, epsilon, delta (and c, lambda, lambda'
// through the same recipe), and kappa = 17523184/10^25. The parameter system is the
// 2^-59 one (src/parameters.ts). New claims: the displayed G and gap, the three
// simplified recurrence gaps, the guard and Gaussian facts at the new beta and
// epsilon, a scoped supremum G_* = z_*/(5 + 4 z_*) for fixed a, b, C1 = 2, and an
// unachieved design target R <= 356295.

import { type Q, q, add, sub, mul, div, lt, le, eq, twoPow, min, ONE, ZERO, show, toDecimal } from "../rational";
import { margins, minimumMargin, parameterChecks, type Params, type Check } from "../parameters";
import { complexNetwork, ground, pairedBitNetwork } from "../networks";
import { guardChecks, guardConstants, unrolledDepthAtPower } from "../guard";
import { gaussianPointChecks } from "../gaussian";
import { maxSideRoles } from "../ceiling";
import { floorTwoPower, lessThanTwoPowerTimes } from "./logs";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const DOC = "PR1 docs/paired-tuned-parameters.md";
const dec = (digits: string, exp: number) => {
  // a decimal literal "d.ddd" times 10^exp, as an exact rational
  const [i, f = ""] = digits.split(".");
  return mul(q(BigInt(i! + f), TEN(f.length)), exp >= 0 ? q(TEN(exp)) : q(1n, TEN(-exp)));
};

/** The PR's recipe with its own beta, epsilon, delta, kappa (section "Explicit rational parameters"). */
export function pr1Params(): Params {
  return recipe(q(296n, TEN(11)), q(1n, TEN(11)), q(99999912384n, TEN(11)), q(1999999999999n, TEN(13)), q(1n, TEN(14)), q(17523184n, TEN(25)));
}

/** c = beta a, lambda = 1 - (1+beta) a^2/2, lambda' = 1 - beta a^2, C1 = 2. */
export function recipe(a: Q, ac: Q, beta: Q, epsilon: Q, delta: Q, kappa: Q): Params {
  const a2 = mul(a, a);
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    beta,
    epsilon,
    delta,
    C1: q(2n),
    c: mul(beta, a),
    lambda: sub(ONE, mul(div(add(ONE, beta), q(2n)), a2)),
    lambdaPrime: sub(ONE, mul(beta, a2)),
    kappa,
  };
}

/** The design target of the PR (not a claim): a = 417/10^11, beta = 999998/10^6, eps = 1999999/10^7, delta = 10^-8. */
export function pr1DesignParams(): Params {
  return recipe(q(417n, TEN(11)), q(1n, TEN(11)), q(999998n, TEN(6)), q(1999999n, TEN(7)), q(1n, TEN(8)), twoPow(-58));
}

/** Stated numbers (decimals are exact unless marked as approximate). */
export const STATED_PR1 = {
  G: dec("1.7523184646864326407676563456", -18),
  gap: dec("6.46864326407676563456", -26),
  factorOver59: dec("1.0101427831391313610145792", 0),
  Gold: dec("1.7418148416", -18),
  gainOverGoldPercent: dec("0.6030238", 0), // "approximately 0.6030238%"
  onePiece: dec("1.00000350464", 0),
  gammaExponent: dec("0.79999999999985", 0),
  g5: dec("1.15", -13),
  supremum: dec("1.7523184646886585106200710664", -18), // "approximately"
  supremumFraction: dec("0.99999996", 0), // "exceeds 99.999996% of this supremum"
  designRmax: 356295n,
  designMinMargin: dec("3.47777130555347778", -18), // displayed; compared to its last digit
};

/** Enclose z_* = smaller root of a z^2 - (b + a^2) z + a^2 b by an integer square root (not by bisection). */
export function supremumBySqrt(a: Q, b: Q, digits = 80) {
  const B = add(b, mul(a, a));
  const disc = sub(mul(B, B), mul(q(4n), mul(mul(a, a), mul(a, b)))); // (b+a^2)^2 - 4 a^3 b
  // sqrt(disc) in [r/S, (r+1)/S] with S = 10^digits, r = floor(sqrt(disc) S)
  const S = TEN(digits);
  const scaled = (disc.num * S * S) / disc.den; // floor(disc S^2)
  let r = isqrt(scaled);
  const lo = q(r, S);
  const hi = q(r + 1n, S);
  if (!(le(mul(lo, lo), disc) && lt(disc, mul(hi, hi)))) throw new Error("sqrt enclosure failed");
  const num = mul(q(2n), mul(mul(a, a), b));
  // z = 2 a^2 b / (B + sqrt(disc)) is decreasing in sqrt(disc)
  const z = { lower: div(num, add(B, hi)), upper: div(num, add(B, lo)) };
  const G = { lower: div(z.lower, add(q(5n), mul(q(4n), z.lower))), upper: div(z.upper, add(q(5n), mul(q(4n), z.upper))) };
  return { z, G, disc };
}

function isqrt(n: bigint): bigint {
  if (n < 2n) return n;
  // Newton from above: x0 = 2^ceil(bits/2) >= sqrt(n); the iterates decrease to floor(sqrt n)
  let x = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
  for (;;) {
    const y = (x + n / x) >> 1n;
    if (y >= x) return x;
    x = y;
  }
}

/** The quadratic p(z) = a z^2 - (b+a^2) z + a^2 b (the PR's boxed equation). */
export const supQuadratic = (a: Q, b: Q, z: Q) => add(sub(mul(a, mul(z, z)), mul(add(b, mul(a, a)), z)), mul(mul(a, a), b));

/**
 * Gaussian instance b = 2^k with d = floor(b^eps), by logarithm enclosures (the
 * exponent denominator 10^13 rules out the integer comparisons of src/gaussian.ts).
 */
export function gaussianInstanceByLogs(k: number, epsilon: Q) {
  const b = 1n << BigInt(k);
  const d = floorTwoPower(mul(q(BigInt(k)), epsilon));
  const pc = gaussianPointChecks(d, b);
  const e = add(q(1n, 2n), mul(q(3n, 2n), epsilon));
  const ok =
    pc.alphaFourthCovers &&
    pc.resamplingMargin &&
    pc.eightBAboveP &&
    pc.alphaAtMostTwiceRoot &&
    pc.gammaBelow46 &&
    pc.alpha >= 2n &&
    pc.alpha * pc.alpha < 6n * b &&
    4n * pc.gamma <= b &&
    lessThanTwoPowerTimes(pc.gamma, 46n, k, e); // gamma < 46 b^e
  return { b, d, alpha: pc.alpha, gamma: pc.gamma, ok };
}

/**
 * Depth recurrence samples for beta near 1 (1 - beta = 1369/1562500000). With d = m^K
 * the stopping test is e^v < d^u, i.e. v k < u K on e = m^k; it is evaluated exactly.
 * The bound A <= s(8+E) d^(5-4 beta) is checked through the stronger A <= s(8+E) d
 * (5 - 4 beta > 1), and A <= 9 B^2 d likewise; j <= (1-beta) K + 1 exactly.
 */
export function depthSamplesNearOne(m: bigint, s: bigint, E: bigint, B: bigint, beta: Q) {
  let ok = true;
  let cases = 0;
  let maxJ = 0;
  for (const K of [1, 2, 10, 250, 1000]) {
    const d = m ** BigInt(K);
    for (let k = Math.max(0, K - 3); k <= K; k++) {
      const { A, j } = unrolledDepthAtPower(k, K, m, s, E, beta);
      cases++;
      maxJ = Math.max(maxJ, j);
      const jOk = beta.den * BigInt(j - 1) <= (beta.den - beta.num) * BigInt(K);
      if (!(jOk && A <= s * (8n + E) * d && A <= 9n * B * B * d)) ok = false;
    }
  }
  return { ok, detail: `${cases} roots, up to ${maxJ} internal levels` };
}

export type PR1Options = { p?: Params; stated?: Partial<typeof STATED_PR1> };

export function pr1(opts: PR1Options = {}) {
  const p = opts.p ?? pr1Params();
  const st = { ...STATED_PR1, ...opts.stated };
  const out: Result[] = [];
  const g = margins(p);
  const G = minimumMargin(p);
  const a = p.a;
  const b = p.ac;
  const a2 = mul(a, a);

  // ---- 1A: the unchanged networks
  const S0 = "PR1-A unchanged networks (h = 50)";
  const cx = complexNetwork(50);
  const L0 = q(11737n, 1000n);
  out.push(
    fromCheck(S0, { name: "eta_c > a_c L0 (complex network unchanged, a_c = 1/10^11)", source: DOC + ", Guard and Gaussian dependencies", lhs: mul(p.ac, L0), rel: "<", rhs: cx.eta }),
    fromCheck(S0, {
      name: "eta_b > a_b L0 at R = 509194 (bit network unchanged; certified by B1, B2 of `bun run check`)",
      source: DOC + ", Result",
      lhs: mul(a, L0),
      rel: "<",
      rhs: pairedBitNetwork(50, 509194n).eta,
      kind: "implied",
    }),
  );

  // ---- 1B: parameter conditions of the 2^-59 system at the new parameters
  const SB = "PR1-B parameters, the thirty side conditions, margins";
  out.push(...parameterChecks(p).map((k) => fromCheck(SB, k)));
  out.push(
    equals(SB, "G = min g_j (decimal 1.7523184646864326407676563456e-18)", DOC + ", seven margins", G, st.G),
    truth(SB, "G = g2 = g3 (limiting margins)", DOC, eq(G, g.g2) && eq(G, g.g3) && lt(G, g.g1) && lt(G, g.g4) && lt(G, g.g5) && lt(G, g.g6) && lt(G, g.g7)),
    equals(SB, "G - kappa = 6.46864326407676563456e-26", DOC, sub(G, p.kappa), st.gap),
    equals(SB, "g5 = 1/4 - delta - 5 eps/4 = 1.15e-13", DOC + ", Guard and Gaussian dependencies", g.g5, st.g5),
    equals(SB, "kappa = 17523184/10^25 (as stated in Result)", DOC + ", Result", p.kappa, q(17523184n, TEN(25)), "identity"),
    equals(SB, "kappa / 2^-59 = 1.0101427831391313610145792", DOC + ", Result", mul(p.kappa, twoPow(59)), st.factorOver59),
    equals(SB, "G_old = 0.199 * 0.999 * a^2 = 1.7418148416e-18", DOC + ", Result", mul(mul(q(199n, 1000n), q(999n, 1000n)), a2), st.Gold),
    truth(
      SB,
      "kappa / G_old - 1 = 0.6030238% (to the stated 7 digits)",
      DOC + ", Result: approximately 0.6030238%",
      lt(absQ(sub(mul(sub(div(p.kappa, st.Gold), ONE), q(100n)), st.gainOverGoldPercent)), q(5n, TEN(8))),
      `${toDecimal(mul(sub(div(p.kappa, st.Gold), ONE), q(100n)), 12)} %`,
    ),
    // the three simplified recurrence checks are algebraic identities of the recipe
    equals(SB, "lambda - tau(1 + c/beta) = (1-beta) a^2 / 2", DOC + ", delicate recurrence checks", sub(p.lambda, mul(p.tau, add(ONE, div(p.c, p.beta)))), mul(div(sub(ONE, p.beta), q(2n)), a2), "identity"),
    equals(SB, "lambda' - lambda = (1-beta) a^2 / 2", DOC, sub(p.lambdaPrime, p.lambda), mul(div(sub(ONE, p.beta), q(2n)), a2), "identity"),
    equals(SB, "lambda' - [sigma + beta(1-sigma)] = (1-beta) b - beta a^2", DOC, sub(p.lambdaPrime, add(p.sigma, mul(p.beta, sub(ONE, p.sigma)))), sub(mul(sub(ONE, p.beta), b), mul(p.beta, a2)), "identity"),
  );
  // "Retuning epsilon without shrinking delta would also fail: the old delta = 10^-4 is incompatible"
  const oldDelta = { ...p, delta: q(1n, 10000n) };
  out.push(truth(SB, "with the old delta = 10^-4 the Gaussian condition 3/4 + delta + 5 eps/4 < 1 fails (as stated)", DOC, !lt(add(add(q(3n, 4n), oldDelta.delta), mul(q(5n, 4n), p.epsilon)), ONE)));

  // ---- 1C: stopped guard at the new beta (complex network h = 50 unchanged)
  const SC = "PR1-C stopped guard (beta = 99999912384/10^11, C1 = 2)";
  const gc = guardConstants(cx.W, cx.s, ground(50).m);
  out.push(...guardChecks(cx.W, cx.s, ground(50).m, p.beta, p.C1).map((k) => fromCheck(SC, k)));
  out.push(
    equals(SC, "5 - 4 beta = 1.00000350464", DOC, sub(q(5n), mul(q(4n), p.beta)), st.onePiece),
    fromCheck(SC, { name: "5 - 4 beta + 1/2 < 2 = C1", source: DOC, lhs: add(sub(q(5n), mul(q(4n), p.beta)), q(1n, 2n)), rel: "<", rhs: p.C1, kind: "condition" }),
  );
  const depth = cached(`pr1 depth ${show(p.beta)}`, () => depthSamplesNearOne(ground(50).m, cx.s, gc.E, gc.B, p.beta));
  out.push(truth(SC, "unrolled depth recurrence: j <= (1-beta) log_m d + 1, A <= s(8+E) d and A <= 9B^2 d (sufficient, since 5 - 4 beta > 1)", "stopped-guard.tex", depth.ok, depth.detail));

  // ---- 1D: Gaussian width at the new epsilon
  const SD = "PR1-D Gaussian width (eps = 1999999999999/10^13)";
  const ge = add(q(1n, 2n), mul(q(3n, 2n), p.epsilon));
  out.push(
    fromCheck(SD, { name: "(8 sqrt 32)^2 = 2048 < 46^2", source: "eq:gamma", lhs: q(2048n), rel: "<", rhs: q(46n * 46n), kind: "constant" }),
    equals(SD, "gamma exponent 1/2 + 3 eps/2 = 0.79999999999985", DOC, ge, st.gammaExponent),
    fromCheck(SD, { name: "gamma exponent < 4/5", source: DOC + ": 46 B0^(1/2+3eps/2) < 46 B0^(4/5)", lhs: ge, rel: "<", rhs: q(4n, 5n), kind: "condition" }),
    fromCheck(SD, { name: "184 < 2^8 (so B0 >= 2^40 gives 46 B0^(4/5) <= B0/4)", source: DOC, lhs: q(184n), rel: "<", rhs: q(256n), kind: "constant" }),
  );
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`pr1 gauss ${e} ${show(p.epsilon)}`, () => {
      try {
        return gaussianInstanceByLogs(e, p.epsilon);
      } catch (err) {
        return { ok: false, d: 0n, alpha: 0n, gamma: 0n, b: 0n, err: String(err) };
      }
    });
    out.push(truth(SD, `b = 2^${e}: alpha, gamma meet every stated bound (d by log enclosures)`, DOC, r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }

  // ---- 1E: the scoped supremum for fixed a, b, C1 = 2
  const SE = "PR1-E scoped supremum G_* = z_*/(5 + 4 z_*) (fixed a, b, C1 = 2)";
  const sup = supremumBySqrt(a, b);
  out.push(
    fromCheck(SE, { name: "a^2 < b/10 (the crossing has beta >= 9/10)", source: DOC + ", Exact supremum", lhs: a2, rel: "<", rhs: div(b, q(10n)), kind: "condition" }),
    truth(SE, "p(0) > 0 > p(a^2) for p(z) = a z^2 - (b + a^2) z + a^2 b", DOC, lt(ZERO, supQuadratic(a, b, ZERO)) && lt(supQuadratic(a, b, a2), ZERO)),
    truth(SE, "the sqrt enclosure of z_* brackets a sign change of p (second route; the PR bisects)", DOC, lt(ZERO, supQuadratic(a, b, sup.z.lower)) && lt(supQuadratic(a, b, sup.z.upper), ZERO)),
    truth(SE, "z_* < a^2 < min{a, b}", DOC, lt(sup.z.upper, a2) && lt(a2, min(a, b))),
    truth(
      SE,
      "G_* ~ 1.7523184646886585106200710664e-18 (enclosure within half a unit of the last stated digit)",
      DOC,
      le(sub(st.supremum, q(5n, TEN(47))), sup.G.lower) && lt(sup.G.upper, add(st.supremum, q(5n, TEN(47)))),
      `[${toDecimal(mul(sup.G.lower, q(TEN(18))), 30)}, ${toDecimal(mul(sup.G.upper, q(TEN(18))), 30)}] e-18`,
    ),
    fromCheck(SE, { name: "the explicit witness is below the supremum: G <= G_*", source: DOC + " (consistency: G_* is a supremum over these parameters)", lhs: G, rel: "<", rhs: sup.G.lower }),
    fromCheck(SE, { name: "kappa > 99.999996% of G_*", source: DOC, lhs: mul(st.supremumFraction, sup.G.upper), rel: "<", rhs: p.kappa }),
    fromCheck(SE, { name: "G_* < 2^-58", source: DOC, lhs: sup.G.upper, rel: "<", rhs: twoPow(-58) }),
  );

  // ---- 1F: the design target (an unachieved target, not a claim of the PR)
  const SF = "PR1-F design target (stated as UNACHIEVED; not part of the claim)";
  const dp = pr1DesignParams();
  const dpChecks: Check[] = parameterChecks(dp);
  const failing = dpChecks.filter((k) => !(k.rel === "<" ? lt(k.lhs, k.rhs) : le(k.lhs, k.rhs))).map((k) => k.name);
  out.push(
    equals(SF, "largest R with eta_b(R) > (417/10^11)(11737/1000) is 356295", DOC + ", A concrete next-network target", maxSideRoles(50, q(417n, TEN(11)), L0), st.designRmax),
    truth(SF, "all parameter conditions hold for the design parameters (kappa replaced by 2^-58)", DOC, failing.length === 0, failing.join("; ")),
    truth(
      SF,
      "design minimum margin = 3.47777130555347778e-18 (to the stated digits) and > 2^-58",
      DOC,
      lt(absQ(sub(minimumMargin(dp), st.designMinMargin)), q(1n, TEN(35))) && lt(twoPow(-58), minimumMargin(dp)),
      toDecimal(mul(minimumMargin(dp), q(TEN(18))), 20),
    ),
  );
  for (const r of out) if (r.section === SF && r.kind === "check") r.kind = "observation";

  return { results: out, values: { params: p, margins: g, G, guard: gc, complex: cx, supremum: sup, depth } };
}

const absQ = (x: Q) => (x.num < 0n ? q(-x.num, x.den) : x);
