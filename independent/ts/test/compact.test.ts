// The compact-control witness kappa = 83/10^12: the published values pass, and
// each nudge just past a stated limit makes the matching inequality fail.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, lt, le, eq, twoPow, ONE, type Q } from "../src/rational";
import { holds, parameterChecks, type Check } from "../src/parameters";
import { complexNetwork, ground, pairedBitNetwork } from "../src/networks";
import { logIntegerEnclosure, logEnclosureNearOne } from "../src/log";
import { compactParams, compactParameterChecks, compactMarginChecks, compactStatedValues, compactMinimumMargin, layerExponents, type CompactParams } from "../src/compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers, depthTable } from "../src/compact/guard";
import { savingEnclosure, minusLogOneMinusEnclosure } from "../src/compact/ceiling";
import { allocation, repairBound, digitIdentityExhaustive, fourUpdates, guardWidth, ceilLog } from "../src/compact/layout";
import { gaussianChecks, gaussianPointChecks, dimensionFromB, cutoffSuffices } from "../src/gaussian";
import { ceilRoot } from "../src/intmath";
import { compactWitnessChecks, L0_COMPLEX } from "../src/checks";

const P = compactParams();
const TEN = (k: number) => 10n ** BigInt(k);
const names = (ks: Check[]) => ks.filter((k) => !holds(k)).map((k) => k.name);
/** All parameter and margin checks that fail for a modified parameter set. */
const failing = (p: CompactParams) => [...names(compactParameterChecks(p)), ...names(compactMarginChecks(p))];
/** Recompute C1 = 5 - 4 beta + zeta after changing beta or zeta, as the note's definition requires. */
const withGuard = (p: CompactParams): CompactParams => ({ ...p, C1: add(sub(q(5n), mul(q(4n), p.beta)), p.zeta) });
const withSavings = (a: Q, ac: Q): CompactParams => ({ ...P, a, ac, tau: sub(ONE, a), sigma: sub(ONE, ac) });

const cx25 = complexNetwork(25);
const m25 = ground(25).m;
const log25 = logIntegerEnclosure(m25);

describe("published compact-control parameters", () => {
  test("every parameter, margin and stated value holds; 2^-34 < kappa < G_* and kappa < 2^-33", () => {
    expect(failing(P)).toEqual([]);
    expect(compactStatedValues(P).filter((r) => !r.ok)).toEqual([]);
    expect(lt(P.kappa, compactMinimumMargin(P))).toBe(true);
  });
});

describe("failure modes: the claimed exponent", () => {
  test("claiming kappa = G_* fails the strict absorption gap", () => {
    expect(failing({ ...P, kappa: compactMinimumMargin(P) })).toEqual(["kappa < g3", "kappa < G_* = min g_j (strict absorption gap)"]);
  });
  test("claiming kappa = 2^-33 fails (G_* is below 2^-33)", () => {
    const f = failing({ ...P, kappa: twoPow(-33) });
    expect(f).toContain("kappa < G_* = min g_j (strict absorption gap)");
    expect(f).toContain("kappa < 2^-33");
  });
  test("kappa = 2^-34 is supported by every margin (the corollary) but is not strictly above 2^-34", () => {
    expect(failing({ ...P, kappa: twoPow(-34) })).toEqual(["kappa > 2^-34"]);
  });
});

describe("failure modes: each parameter nudged past its limit", () => {
  test("epsilon = 1988/10000 drops g3 = eps(1 - lambda') below kappa", () => {
    expect(failing({ ...P, epsilon: q(1988n, 10000n) })).toEqual(["kappa < g3", "kappa < G_* = min g_j (strict absorption gap)"]);
  });
  test("epsilon at the Gaussian limit 4(1/4 - delta)/5 fails the Gaussian cost", () => {
    const f = failing({ ...P, epsilon: mul(q(4n, 5n), sub(q(1n, 4n), P.delta)) });
    expect(f).toContain("3/4 + delta + 5*epsilon/4 < 1");
  });
  test("lambda' equal to the leaf exponent fails the leaf bound", () => {
    expect(failing({ ...P, lambdaPrime: layerExponents(P).leaf })).toContain("sigma + beta(1-sigma) < lambda'");
  });
  test("1 - lambda' = 415/10^12 keeps the layer conditions but drops g3 below kappa", () => {
    expect(failing({ ...P, lambdaPrime: sub(ONE, q(415n, TEN(12))) })).toEqual(["kappa < g3", "kappa < G_* = min g_j (strict absorption gap)"]);
  });
  test("lambda = sigma fails sigma < lambda; lambda = lambda' fails lambda < lambda'; lambda = chi fails chi < lambda", () => {
    expect(failing({ ...P, lambda: P.sigma })).toContain("sigma < lambda");
    expect(failing({ ...P, lambda: P.lambdaPrime })).toContain("lambda < lambda'");
    expect(failing({ ...P, lambda: layerExponents(P).chi })).toContain("chi < lambda");
  });
  test("a_b = 207/10^11 drops g2 = eps c (1 - tau) below kappa", () => {
    expect(failing(withSavings(q(207n, TEN(11)), P.ac))).toEqual(["kappa < g2", "kappa < G_* = min g_j (strict absorption gap)"]);
  });
  test("a_b = 297/10^11 is not supported by the bit network (eta_b^pair <= a L0)", () => {
    const etaB = pairedBitNetwork(50, 509194n).eta;
    expect(lt(mul(q(297n, TEN(11)), q(11737n, 1000n)), etaB)).toBe(false);
    expect(lt(mul(q(296n, TEN(11)), q(11737n, 1000n)), etaB)).toBe(true);
  });
  test("a_c = 419/10^12 exceeds the actual complex saving (and fails eta_c > a_c * 966/100)", () => {
    const p = withSavings(P.a, q(419n, TEN(12)));
    expect(compactWitnessChecks(p, 25).complexSupported).toBe(false);
    expect(lt(mul(p.ac, L0_COMPLEX), cx25.eta)).toBe(false);
    expect(lt(savingEnclosure(cx25.eta, log25).upper, p.ac)).toBe(true); // a* < 419/10^12 outright
  });
  test("a_c = 417/10^12 fails the leaf bound and sigma < lambda", () => {
    const f = failing(withSavings(P.a, q(417n, TEN(12))));
    expect(f).toContain("sigma + beta(1-sigma) < lambda'");
    expect(f).toContain("sigma < lambda");
  });
  test("c = 14/100 drops g2 below kappa; c = 0 fails the reservation exponent 1 - c < lambda'", () => {
    expect(failing({ ...P, c: q(14n, 100n) })).toEqual(["kappa < g2", "kappa < G_* = min g_j (strict absorption gap)"]);
    const f = failing({ ...P, c: q(0n) });
    expect(f).toContain("max{1-c,0} < lambda'");
    expect(f).toContain("c > 0");
  });
  test("beta = 2/1000 (C1 recomputed) fails the leaf bound; beta = 0 and beta = 1 fail 0 < beta < 1", () => {
    expect(failing(withGuard({ ...P, beta: q(2n, 1000n) }))).toEqual(["sigma + beta(1-sigma) < lambda'"]);
    expect(failing(withGuard({ ...P, beta: q(0n) }))).toContain("beta > 0");
    expect(failing(withGuard({ ...P, beta: ONE }))).toContain("beta < 1");
  });
  test("zeta = 7/1000 (C1 recomputed) fails eps C1 < 1; zeta = 0 fails zeta > 0", () => {
    expect(failing(withGuard({ ...P, zeta: q(7n, 1000n) }))).toEqual(["epsilon*C1 < 1"]);
    expect(failing(withGuard({ ...P, zeta: q(0n) }))).toContain("zeta > 0");
  });
  test("delta = 125/10^6 closes the Gaussian margin; delta = 1/8 fails the resampling hypothesis", () => {
    expect(failing({ ...P, delta: q(125n, TEN(6)) })).toContain("3/4 + delta + 5*epsilon/4 < 1");
    expect(failing({ ...P, delta: q(1n, 8n) })).toContain("delta < 1/8");
  });
  test("epsilon = 1/3 fails epsilon < 1/3", () => {
    expect(failing({ ...P, epsilon: q(1n, 3n) })).toContain("epsilon < 1/3");
  });
});

describe("why the compact primitive matters", () => {
  test("with the earlier wide-slot overhead (an extra K^tau, theta = tau) the internal exponent exceeds lambda", () => {
    expect(names(compactParameterChecks(P, P.tau))).toEqual(["chi < lambda"]);
  });
  test("the earlier packed-overhead condition tau(1 + c/beta) < lambda fails for these parameters", () => {
    expect(names(parameterChecks(P))).toContain("tau(1+c/beta) < lambda");
  });
});

describe("complex network at h = 25", () => {
  test("L_c < N_c holds but 2 L_c < N_c does not (the note needs only the first)", () => {
    const N = ground(25).N;
    expect(cx25.L < N).toBe(true);
    expect(2n * cx25.L < N).toBe(false);
  });
  test("log m_c < 966/100 by the atanh enclosure, and 966/100 cannot be lowered to 965/100", () => {
    expect(lt(log25.upper, L0_COMPLEX)).toBe(true);
    expect(lt(q(965n, 100n), log25.lower)).toBe(true);
  });
  test("the Mercator enclosure of -log(1 - x) overlaps the atanh enclosure of log(1/(1-x)) at x = eta_c (two methods)", () => {
    const x = cx25.eta;
    const merc = minusLogOneMinusEnclosure(x);
    const at = logEnclosureNearOne(div(ONE, sub(ONE, x)), 3); // 1 <= 1/(1-x) <= 2
    expect(le(merc.lower, at.upper) && le(at.lower, merc.upper)).toBe(true);
    // and it sits between the elementary bounds x <= -log(1-x) <= x/(1-x)
    expect(le(x, merc.lower) && lt(merc.lower, merc.upper) && le(merc.upper, div(x, sub(ONE, x)))).toBe(true);
  });
});

describe("generalized guard", () => {
  const { E, B } = compactGuardConstants(cx25.W, cx25.s, m25, P.zeta);
  test("all guard comparisons hold at h_c = 25", () => {
    expect(names(compactGuardChecks(cx25.W, cx25.s, m25, P.beta, P.zeta, P.C1))).toEqual([]);
  });
  test("C0 = ceil(max{128 m B^2, 18 m B^2 (1 + 1/zeta)}) = 180018 m B^2 here", () => {
    expect(compactGuardConstants(cx25.W, cx25.s, m25, P.zeta).C0).toBe(180018n * m25 * B * B);
  });
  test("s = m^5 fails s < m^5; s >= E/4 fails the one-invocation depth bound", () => {
    expect(names(compactGuardChecks(cx25.W, m25 ** 5n, m25, P.beta, P.zeta, P.C1))).toContain("s < m^5");
    expect(names(compactGuardChecks(cx25.W, E / 4n + 1n, m25, P.beta, P.zeta, P.C1))).toContain("24W^3 + 4s + 4W + 4 < E");
  });
  test("the old C1 = 2 with beta = 1/1000 contradicts C1 = 5 - 4 beta + zeta", () => {
    expect(names(compactGuardChecks(cx25.W, cx25.s, m25, P.beta, P.zeta, q(2n)))).toContain("C1 = 5 - 4 beta + zeta (>=)");
  });
  test("unrolled recurrence obeys the stated bound at d = m^1000 and m^2000", () => {
    expect(depthSamplesAtPowers([1000, 2000], m25, cx25.s, E, B, P.beta).ok).toBe(true);
    const { j } = depthTable(2000, m25, cx25.s, E, P.beta);
    expect(j[2000]).toBe(1999); // e^1000 < d stops at e = m: internal levels k = 2..2000
  });
  test("failure mode: a branching factor s = m^6 would outgrow s(8+E) d^(5-4beta)", () => {
    expect(depthSamplesAtPowers([1000], m25, m25 ** 6n, E, B, P.beta).ok).toBe(false);
  });
});

describe("Gaussian width at eps = 1999/10000", () => {
  const eps = P.epsilon;
  test("stated exponents and the cutoff b >= 2^40 hold; b >= 2^37 does not suffice", () => {
    expect(gaussianChecks(eps, q(15997n, 20000n), "test").filter((k) => !holds(k))).toEqual([]);
    expect(cutoffSuffices(eps, 40n)).toBe(true);
    expect(cutoffSuffices(eps, 37n)).toBe(false);
  });
  test("failure mode: the upstream width (12 d^2 b)^(1/4) breaks gamma < 46 d^(3/2) sqrt b at b = 2^40", () => {
    const b = 1n << 40n;
    const d = dimensionFromB(b, eps);
    expect(gaussianPointChecks(d, b).gammaBelow46).toBe(true);
    expect(gaussianPointChecks(d, b, ceilRoot(12n * d * d * b, 4)).gammaBelow46).toBe(false);
  });
});

describe("scoped ceiling", () => {
  const enc = savingEnclosure(cx25.eta, log25);
  test("upper/5 < 8.369598075e-11 < 2^-33 and kappa exceeds 99% of upper/5", () => {
    const u5 = div(enc.upper, q(5n));
    expect(lt(u5, q(8369598075n, TEN(20)))).toBe(true);
    expect(lt(mul(q(99n, 100n), u5), P.kappa)).toBe(true);
  });
  test("failure mode: kappa = 837/10^13 is above upper/5, so no parameters in this family reach it", () => {
    expect(lt(div(enc.upper, q(5n)), q(837n, TEN(13)))).toBe(true);
    expect(failing({ ...P, kappa: q(837n, TEN(13)) })).toContain("kappa < G_* = min g_j (strict absorption gap)");
  });
});

describe("layout and repair arithmetic", () => {
  test("the individual-kernel fallback switches exactly at D = Q_0", () => {
    const d = 10n ** 30n;
    const a = allocation(d, d, 10n ** 6n, 2014n, m25, cx25.W);
    const at = allocation(d, a.reserved_chunks, 10n ** 6n, 2014n, m25, cx25.W);
    const above = allocation(d, a.reserved_chunks + 1n, 10n ** 6n, 2014n, m25, cx25.W);
    expect([at.mode, at.active_chunks]).toEqual(["individual", 0n]);
    expect([above.mode, above.active_chunks]).toEqual(["recursive", 1n]);
  });
  test("G = 4 ceil(log2 p) + 6 at powers of two and their neighbours", () => {
    expect([guardWidth(2n), guardWidth(16n), guardWidth(17n), guardWidth(10n ** 10n)]).toEqual([10, 22, 26, 142]);
    expect([ceilLog(1n, 2n), ceilLog(2n, 2n), ceilLog(3n, 2n)]).toEqual([0, 1, 2]);
  });
  test("failure mode: one bit below the cutoff K = G + 4 ceil(log2 p) + 10 the bound 5/(128 p^3) fails at p = 2^k", () => {
    for (const p of [2n, 16n, 1024n]) {
      const G = BigInt(guardWidth(p));
      const ell = BigInt(ceilLog(p, 2n));
      expect(repairBound(p, p, G + 4n * ell + 10n).ok).toBe(true);
      const r = repairBound(p, p, G + 4n * ell + 9n);
      expect(r.cutoff || r.ok).toBe(false);
    }
  });
  test("the four updates toggle exactly the parity of v when z = 1 and restore any integer temporary", () => {
    for (const [v, z, w] of [[7n, 1n, -5n], [-4n, 1n, 1000n], [9n, 0n, 3n]] as const) {
      const r = fourUpdates(v, z, w);
      expect(r.w).toBe(w);
      expect(r.v - v).toBe(z === 0n ? 0n : ((v % 2n) + 2n) % 2n === 0n ? 1n : -1n);
    }
  });
  test("failure mode: a saturated digit B - 1 (declared bad by the note) overflows its digit", () => {
    const good = digitIdentityExhaustive(5, 3);
    expect(good.identity && good.loadWithinDigit && good.displacementWithin2B && good.laterSourceParity).toBe(true);
    const bad = digitIdentityExhaustive(5, 3, true);
    expect(bad.loadWithinDigit).toBe(false);
    expect(bad.laterSourceParity).toBe(false);
  });
});
