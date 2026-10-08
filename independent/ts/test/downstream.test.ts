// Downstream inequalities: the published values pass, and each one fails when
// nudged just past its limit. A checker that cannot fail proves nothing.
import { describe, expect, test } from "bun:test";
import { q, mul, sub, add, lt, twoPow, eq } from "../src/rational";
import { noteParams, recipeParams, parameterChecks, recurrenceChecks, holds, minimumMargin, margins, marginsFromCostTable, type Params } from "../src/parameters";
import { complexNetwork, pairedBitNetwork, ground } from "../src/networks";
import { logIntegerEnclosure } from "../src/log";
import { guardChecks, guardConstants, unrolledDepthAtPower } from "../src/guard";
import { gaussianChecks, gaussianPointChecks, dimensionFromB, cutoffSuffices } from "../src/gaussian";
import { ceilRoot } from "../src/intmath";
import { maxSideRoles, fixedNetworkCeiling } from "../src/ceiling";
import { depthSamples } from "../src/checks";

const TEN11 = 10n ** 11n;
const L0 = q(11737n, 1000n);
const R = 509194n;
const etaB = pairedBitNetwork(50, R).eta;
const etaC = complexNetwork(50).eta;
const logm = logIntegerEnclosure(125000n);

const failing = (p: Params) => parameterChecks(p).filter((k) => !holds(k)).map((k) => k.name);
const failingRecurrence = (p: Params, eb = etaB, ec = etaC) =>
  recurrenceChecks(eb, ec, L0, logm.upper, p).filter((k) => !holds(k)).map((k) => k.name);

describe("published parameters", () => {
  test("every parameter and recurrence check passes, G > 2^-59", () => {
    const p = noteParams();
    expect(failing(p)).toEqual([]);
    expect(failingRecurrence(p)).toEqual([]);
    expect(lt(twoPow(-59), minimumMargin(p))).toBe(true);
  });
});

describe("failure modes: the claimed bound", () => {
  test("claiming kappa = 2^-58 fails the final margin", () => {
    expect(failing({ ...noteParams(), kappa: twoPow(-58) })).toEqual(["kappa < G = min g_j"]);
  });
  test("claiming kappa = G exactly fails (the comparison is strict)", () => {
    const p = noteParams();
    expect(failing({ ...p, kappa: minimumMargin(p) })).toEqual(["kappa < G = min g_j"]);
  });
});

describe("failure modes: the bit saving a_b is pinned from both sides", () => {
  test("a_b = 297/10^11 breaks eta_b > a L0 (the circuit cannot support it)", () => {
    const p = recipeParams(q(297n, TEN11), q(1n, TEN11));
    expect(failingRecurrence(p)).toEqual(["eta_b > a*L0"]);
  });
  test("a_b = 295/10^11 makes G drop below 2^-59", () => {
    const p = recipeParams(q(295n, TEN11), q(1n, TEN11));
    expect(failing(p)).toEqual(["kappa < G = min g_j"]);
    expect(failingRecurrence(p)).toEqual([]);
  });
  test("a_c = 2/10^11 breaks eta_c > a_c L0", () => {
    expect(failingRecurrence(recipeParams(q(296n, TEN11), q(2n, TEN11)))).toEqual(["eta_c > a_c*L0"]);
  });
  test("one role over the budget breaks eta_b > a L0; the budget itself passes", () => {
    const Rmax = maxSideRoles(50, q(296n, TEN11), L0);
    expect(Rmax).toBeGreaterThanOrEqual(R);
    expect(failingRecurrence(noteParams(), pairedBitNetwork(50, Rmax).eta)).toEqual([]);
    expect(failingRecurrence(noteParams(), pairedBitNetwork(50, Rmax + 1n).eta)).toEqual(["eta_b > a*L0"]);
  });
});

describe("failure modes: epsilon is squeezed between G and the Gaussian margin", () => {
  test("epsilon at the Gaussian limit 4(1/4 - delta)/5 fails g5 > 0", () => {
    const p = noteParams();
    const limit = mul(q(4n, 5n), sub(q(1n, 4n), p.delta));
    const f = failing({ ...p, epsilon: limit });
    expect(f).toContain("g5 > 0");
    expect(f).toContain("3/4 + delta + 5*epsilon/4 < 1");
  });
  test("epsilon = 198/1000 makes G drop below 2^-59", () => {
    expect(failing({ ...noteParams(), epsilon: q(198n, 1000n) })).toEqual(["kappa < G = min g_j"]);
  });
  test("the upstream Gaussian width (alpha exponent 1/4 + eps/2) makes the Gaussian row margin non-positive at epsilon = 199/1000", () => {
    const p = noteParams();
    expect(lt(q(0n), marginsFromCostTable(p).g5)).toBe(true);
    const upstreamAlpha = add(q(1n, 4n), mul(q(1n, 2n), p.epsilon)); // 1/4 + eps/2
    expect(lt(q(0n), marginsFromCostTable(p, upstreamAlpha).g5)).toBe(false);
  });
  test("epsilon = 1/3 fails epsilon < 1/3 (the dimension bound of the Gaussian setup)", () => {
    expect(failing({ ...noteParams(), epsilon: q(1n, 3n) })).toContain("epsilon < 1/3");
  });
  test("the old guard exponent C1 = 20 would fail epsilon*C1 < 1", () => {
    expect(failing({ ...noteParams(), C1: q(20n) })).toEqual(["epsilon*C1 < 1"]);
  });
});

describe("failure modes: layer conditions", () => {
  test("lambda equal to tau(1+c/beta) = 1 - a^2 fails the strict packed-overhead bound", () => {
    const p = noteParams();
    expect(failing({ ...p, lambda: sub(q(1n), mul(p.a, p.a)) })).toContain("tau(1+c/beta) < lambda");
  });
  test("lambda' equal to lambda fails", () => {
    const p = noteParams();
    expect(failing({ ...p, lambdaPrime: p.lambda })).toContain("lambda < lambda'");
  });
  test("beta = 1 fails beta < 1; beta = 89/100 fails beta >= 9/10", () => {
    expect(failing({ ...noteParams(), beta: q(1n) })).toContain("beta < 1");
    expect(failing({ ...noteParams(), beta: q(89n, 100n) })).toContain("beta >= 9/10");
  });
  test("lambda' equal to the leaf exponent sigma + beta(1 - sigma) fails the leaf-cost bound", () => {
    const p = noteParams();
    const leaf = sub(q(1n), mul(sub(q(1n), p.beta), sub(q(1n), p.sigma)));
    expect(failing({ ...p, lambdaPrime: leaf })).toContain("sigma + beta(1-sigma) < lambda'");
  });
  test("delta = 1/8 fails the resampling hypothesis", () => {
    expect(failing({ ...noteParams(), delta: q(1n, 8n) })).toContain("delta < 1/8");
  });
});

describe("stopped guard", () => {
  const { W, s } = complexNetwork(50);
  const m = ground(50).m;
  const p = noteParams();
  test("all integer comparisons pass at h = 50", () => {
    expect(guardChecks(W, s, m, p.beta, p.C1).filter((k) => !holds(k))).toEqual([]);
  });
  test("beta = 89/100 fails the guard exponent requirements", () => {
    const f = guardChecks(W, s, m, q(89n, 100n), p.C1).filter((k) => !holds(k)).map((k) => k.name);
    expect(f).toContain("beta >= 9/10 (guard)");
  });
  test("s >= m^5 would break s^j <= s d^(5(1-beta))", () => {
    const f = guardChecks(W, m ** 5n, m, p.beta, p.C1).filter((k) => !holds(k)).map((k) => k.name);
    expect(f).toContain("s < m^5");
  });
  test("a rank sum s >= E/4 would break the one-invocation depth bound 24W^3 + 4s + 4W + 4 < E", () => {
    const { E } = guardConstants(W, s, m);
    const f = guardChecks(W, E / 4n + 1n, m, p.beta, p.C1).filter((k) => !holds(k)).map((k) => k.name);
    expect(f).toContain("24W^3 + 4s + 4W + 4 < E");
  });
  test("C1 below 19/10 fails 7/5 + 1/2 <= C1 (the piece count costs d^(1/2))", () => {
    const f = guardChecks(W, s, m, p.beta, q(189n, 100n)).filter((k) => !holds(k)).map((k) => k.name);
    expect(f).toEqual(["7/5 + 1/2 <= C1"]);
  });
  test("the unrolled recurrence obeys both stated bounds (j up to 5)", () => {
    const { E, B } = guardConstants(W, s, m);
    expect(depthSamples(m, s, E, B, p.beta).ok).toBe(true);
  });
  test("depth samples reject a recurrence that outgrows either bound", () => {
    const { E, B } = guardConstants(W, s, m);
    // B = 1: the true recurrence exceeds 9 B^2 d^(7/5) (the second bound alone fails)
    expect(depthSamples(m, s, E, 1n, p.beta).ok).toBe(false);
    // s = m^10 with a huge B: only the intermediate bound s(8+E) d^(251/250) can fail, and it does
    expect(depthSamples(m, m ** 10n, E, B ** 1000n, p.beta).ok).toBe(false);
    // the same inputs with the real s pass, so each failure above is the bound, not the sampler
    expect(depthSamples(m, s, E, B ** 1000n, p.beta).ok).toBe(true);
  });
  test("failure mode: with beta = 4/5 the recurrence outgrows 9 B^2 d^(7/5)", () => {
    const { E, B } = guardConstants(W, s, m);
    const beta = q(4n, 5n);
    const K = 200; // d = m^200, d^(7/5) = m^280 exactly
    const { A, j } = unrolledDepthAtPower(K, K, m, s, E, beta);
    expect(j).toBeGreaterThan(1);
    expect(A > 9n * B * B * m ** 280n).toBe(true);
  });
});

describe("Gaussian width", () => {
  const SRC = "test";
  test("symbolic constants pass", () => {
    expect(gaussianChecks(q(199n, 1000n), q(1597n, 2000n), SRC).filter((k) => !holds(k))).toEqual([]);
  });
  test("failure mode: the constant 45 would not cover 8*sqrt(32)", () => {
    const f = gaussianChecks(q(199n, 1000n), q(1597n, 2000n), SRC, 45n).filter((k) => !holds(k)).map((k) => k.name);
    expect(f).toEqual(["(8*sqrt(32))^2 = 2048 < C^2 for the constant C of eq:gamma"]);
  });
  test("failure mode: a misstated gamma exponent is caught in both directions", () => {
    for (const wrong of [q(1596n, 2000n), q(1598n, 2000n)])
      expect(gaussianChecks(q(199n, 1000n), wrong, SRC).filter((k) => !holds(k)).length).toBe(1);
  });
  test("cutoff: b >= 2^40 suffices for 46 b^(1597/2000) <= b/4; b >= 2^37 does not", () => {
    expect(cutoffSuffices(q(199n, 1000n), 40n)).toBe(true);
    expect(cutoffSuffices(q(199n, 1000n), 37n)).toBe(false);
  });
  test("failure mode: alpha one below the ceiling misses alpha^4 >= 32db; the upstream width (12 d^2 b)^(1/4) breaks gamma < 46 d^(3/2) sqrt b", () => {
    const b = 1n << 40n;
    const d = dimensionFromB(b, q(199n, 1000n)); // 248
    const alpha = ceilRoot(32n * d * b, 4);
    expect(gaussianPointChecks(d, b, alpha - 1n).alphaFourthCovers).toBe(false);
    expect(gaussianPointChecks(d, b, ceilRoot(12n * d * d * b, 4)).gammaBelow46).toBe(false);
  });
  test("failure mode: below the cutoff, at b = 2^20, gamma <= b/4 fails", () => {
    const b = 1n << 20n;
    const d = dimensionFromB(b, q(199n, 1000n));
    const { gamma } = gaussianPointChecks(d, b);
    expect(4n * gamma <= b).toBe(false);
  });
  test("alpha^4 theta > 8b holds for every theta > 1/(4d) on a grid of (d, b)", () => {
    for (let d = 1n; d < 60n; d += 7n)
      for (let b = 1n; b < 10n ** 12n; b = b * 13n + 1n) {
        const c = gaussianPointChecks(d, b);
        expect(c.alphaFourthCovers && c.resamplingMargin && c.alphaAtMostTwiceRoot && c.gammaBelow46).toBe(true);
      }
  });
});

describe("fixed-network ceiling", () => {
  test("a^2/(5(1-a)) with the supremal a is below 2^-58 and above G", () => {
    const { value } = fixedNetworkCeiling(etaB, logm.lower);
    expect(lt(value, twoPow(-58))).toBe(true);
    expect(lt(minimumMargin(noteParams()), value)).toBe(true);
  });
  test("G is exactly eps * beta * a^2 for the recipe, for any a", () => {
    for (const k of [1n, 100n, 296n, 1000n]) {
      const p = recipeParams(q(k, TEN11), q(1n, TEN11));
      expect(eq(minimumMargin(p), mul(mul(p.epsilon, p.beta), mul(p.a, p.a)))).toBe(true);
    }
  });
});

describe("cost table", () => {
  test("closed-form margins equal 1 - row exponent for arbitrary parameters (an identity)", () => {
    let x = 99;
    const r = () => q(BigInt(((x = (Math.imul(x, 1103515245) + 12345) >>> 0) % 1000) + 1), 1001n);
    for (let i = 0; i < 100; i++) {
      const p = { ...noteParams(), tau: r(), epsilon: r(), c: r(), lambdaPrime: r(), delta: r() };
      const a = margins(p);
      const b = marginsFromCostTable(p);
      for (const k of Object.keys(a) as (keyof typeof a)[]) expect(eq(a[k], b[k])).toBe(true);
    }
  });
});
