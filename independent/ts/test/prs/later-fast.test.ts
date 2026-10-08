// PR re-checks of 8 October 2026 (PR 4 head 8c225e6 as "4b", PRs 5 and 6): the fast part.
// Function-level failure modes of the fast-Gaussian system and its lemma constants,
// small instances of PR 6's aligned bit circuit and of PR 4b's retained totals, and
// corrupted inputs that the verifiers must reject.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, lt, le, eq, ONE, type Q } from "../../src/rational";
import { floorRoot } from "../../src/intmath";
import { buildPairedCircuit, PUBLISHED_CONVENTIONS } from "../../src/circuit";
import { standardLabelling, mergeWith, pruneMerged } from "../../src/prs/aligned";
import { mergeGroups, verifyAlignedBit, PR6_OPTIONS, type BitCircuitOptions } from "../../src/prs/alignedBit";
import { buildComplexCircuit } from "../../src/prs/complexCircuit";
import { analyseRetained, sharedRetainedNetwork, scatterIdentity } from "../../src/prs/pr4b";
import { pr5Params, errataRows } from "../../src/prs/pr5";
import { pr6Params, alignedBitNetwork, alignedRoleBudget } from "../../src/prs/pr6";
import {
  fastParameterChecks,
  fastMargins,
  fastMinimumMargin,
  guardBetaThreshold,
  leafAndGuardCompatible,
  piEnclosure,
  stepExcess,
  fastWidthInstance,
  exactPowerInstance,
  isqrt,
  DROPPED,
} from "../../src/prs/fastGaussian";
import { compactParameterChecks } from "../../src/compact/witness";
import { holds } from "../../src/parameters";

const TEN = (k: number) => 10n ** BigInt(k);
const failingChecks = (p: Parameters<typeof fastParameterChecks>[0]) => fastParameterChecks(p).filter((k) => !holds(k)).map((k) => k.name);

describe("PR 5: the fast-Gaussian parameter system", () => {
  const P = pr5Params();
  test("the published parameters satisfy every condition, and kappa < G_* = g3", () => {
    expect(failingChecks(P)).toEqual([]);
    expect(lt(P.kappa, fastMinimumMargin(P))).toBe(true);
    expect(eq(fastMinimumMargin(P), fastMargins(P).g3)).toBe(true);
  });
  test("the dropped conditions fail at eps = 49999/100000 except the alpha exponent (so dropping them is necessary)", () => {
    const old = compactParameterChecks(P).filter((k) => DROPPED.includes(k.name));
    expect(old.filter((k) => !holds(k)).map((k) => k.name).sort()).toEqual(["3/4 + delta + 5*epsilon/4 < 1", "epsilon < 1/3", "gamma exponent 1/2+3*epsilon/2 < 1"].sort());
  });
  const nudge = (label: string, p: typeof P, names: string[]) =>
    test(label, () => {
      const f = failingChecks(p);
      for (const n of names) expect(f).toContain(n);
    });
  nudge("2 eps + delta = 1", { ...P, epsilon: div(sub(ONE, P.delta), q(2n)) }, ["2*epsilon + delta < 1"]);
  const thr = guardBetaThreshold(P);
  nudge("beta at the guard threshold (C1 recomputed): eps C1 = 1", { ...P, beta: thr, C1: sub(add(q(5n), P.zeta), mul(q(4n), thr)) }, ["epsilon*C1 < 1"]);
  nudge("lambda' at the leaf boundary 1 - (1-beta)(1-sigma)", { ...P, lambdaPrime: sub(ONE, mul(sub(ONE, P.beta), sub(ONE, P.sigma))) }, ["sigma + beta(1-sigma) < lambda'"]);
  nudge("eps c = 1 - eps", { ...P, c: div(sub(ONE, P.epsilon), P.epsilon) }, ["epsilon*c < 1 - epsilon"]);
  nudge("delta = 1/8", { ...P, delta: q(1n, 8n) }, ["delta < 1/8"]);
  nudge("lambda = tau", { ...P, lambda: P.tau }, ["tau < lambda", "chi < lambda"]);
  test("g5 is 1 - delta - 2 eps (not the old 1/4 - delta - 5 eps/4)", () => {
    expect(eq(fastMargins(P).g5, q(19n, TEN(6)))).toBe(true);
  });
  test("leaf and guard together: impossible with a_c = 418/10^12, possible with 14/10^9; the boundary a_c is where it switches", () => {
    expect(leafAndGuardCompatible(P, q(418n, TEN(12)))).toBe(false);
    expect(leafAndGuardCompatible(P, P.ac)).toBe(true);
    const boundary = div(div(P.kappa, P.epsilon), sub(ONE, thr));
    expect(leafAndGuardCompatible(P, boundary)).toBe(false);
    expect(leafAndGuardCompatible(P, add(boundary, q(1n, TEN(30))))).toBe(true);
  });
  test("errata rows: the C1 sentence holds at PR 3's eps and fails at PR 5's", () => {
    const at = (eps: Q) => errataRows("t", { ...P, epsilon: eps }, "x", 1, 2);
    expect(at(q(19999n, 100000n)).map((r) => r.ok)).toEqual([true, true]);
    expect(at(P.epsilon).map((r) => r.ok)).toEqual([false, false]);
  });
});

describe("PR 5: lemma constants and samples", () => {
  test("pi enclosure lies in [3.14159265358979323846, 3.14159265358979323847] and is narrower than 10^-30", () => {
    const pi = piEnclosure();
    expect(le(q(314159265358979323846n, TEN(20)), pi.lower) && le(pi.upper, q(314159265358979323847n, TEN(20)))).toBe(true);
    expect(lt(sub(pi.upper, pi.lower), q(1n, TEN(30)))).toBe(true);
    const loose = piEnclosure(1);
    expect(lt(loose.lower, pi.lower) && lt(pi.upper, loose.upper)).toBe(true);
  });
  test("step identity and inequality on every sample (s, t); minimum excess 0", () => {
    for (const [s, t] of [[7, 8], [31, 32], [97, 101], [5, 6], [11, 13]] as const) {
      const r = stepExcess(s, t, 3 * s);
      expect([s, t, r.identity, r.nonneg, r.min.num]).toEqual([s, t, true, true, 0n]);
    }
  });
  test("isqrt agrees with floorRoot on 2000 numbers, including squares and their neighbours", () => {
    let x = 1n;
    for (let i = 0; i < 2000; i++) {
      x = (x * 6364136223846793005n + 1442695040888963407n) % (1n << 90n);
      for (const y of [x, x * x, x * x - 1n, x * x + 1n]) if (y >= 0n && y < 1n << 120n) expect(isqrt(y)).toBe(floorRoot(y, 2));
    }
  });
  test("Gaussian width instance facts fail past their limits", () => {
    const d = 1000n;
    expect(fastWidthInstance(96n * d - 1n, d).facts.bAtLeast96d).toBe(false);
    expect(fastWidthInstance(64n * d * d - 1n, d).facts.bAtLeast64d2).toBe(false);
    expect(fastWidthInstance(64n * d * d, d).facts.bAtLeast64d2).toBe(true);
    // with b < 64 d^2 the bound alpha^2 theta > 1 is no longer guaranteed: at b = 32 d^2,
    // alpha^2 = floor(sqrt(4d))^2 = 3969 < 4d = 4000 and it fails
    expect(fastWidthInstance(32n * d * d, d).facts.alphaSqThetaAtLeast1).toBe(false);
    expect(fastWidthInstance(32n * d * d + 64n * d * 40n, d).facts.alphaSqThetaAtLeast1).toBe(true);
    expect(fastWidthInstance(32n * d, d).facts.alphaAtLeast2).toBe(true);
    expect(fastWidthInstance(31n * d, d).facts.alphaAtLeast2).toBe(false);
    expect(fastWidthInstance(1000n, 2n).facts.dAtLeast3).toBe(false);
  });
  test("exact power instances need k eps integral; at b = 2^300000 every fact holds", () => {
    expect(() => exactPowerInstance(300001, pr5Params().epsilon)).toThrow();
    expect(Object.values(exactPowerInstance(300000, pr5Params().epsilon).facts).every(Boolean)).toBe(true);
  });
});

describe("PR 6: aligned bit circuit on small ground sets", () => {
  for (const h of [8, 10, 12])
    test(`h = ${h}: partial outputs and totals exact, additions disjoint, common point, every node used`, () => {
      for (const conv of [PR6_OPTIONS.conv, PUBLISHED_CONVENTIONS]) {
        const r = verifyAlignedBit(mergeGroups(h, { ...PR6_OPTIONS, conv }));
        expect([r.allPartialOutputsExact, r.totalsExact, r.allAdditionsDisjoint, r.totalsDisjoint, r.everyNodeHasCommonPoint, r.everyNodeUsedWithTotals, r.distinctTotals, r.totalsCount]).toEqual([true, true, true, true, true, true, true, h]);
      }
    });
  test("with consecutive blocks, no shared chains and no totals, the generalised builder reproduces the published merge (h = 10, 12)", () => {
    const opt: BitCircuitOptions = { conv: PUBLISHED_CONVENTIONS, rootBlocks: "consecutive", sharedStars: false, starTripleLast: true, totals: "none" };
    for (const h of [10, 12]) {
      const mine = mergeGroups(h, opt);
      const { graph } = pruneMerged(mergeWith(buildPairedCircuit(h - 1), h, standardLabelling(h)));
      expect([h, mine.left.length, mine.mergedAdditions]).toEqual([h, graph.left.length, graph.mergedAdditions]);
    }
  });
  test("shared chains reduce the count at h = 12", () => {
    const shared = mergeGroups(12, PR6_OPTIONS).left.length;
    const unshared = mergeGroups(12, { ...PR6_OPTIONS, sharedStars: false }).left.length;
    expect(shared).toBeLessThan(unshared);
  });
  test("corrupted graphs are rejected: swapped totals, a swapped partial output", () => {
    const G = mergeGroups(10, PR6_OPTIONS);
    const t = G.totals.slice();
    [t[0], t[1]] = [t[1]!, t[0]!];
    expect(verifyAlignedBit({ ...G, totals: t }).totalsExact).toBe(false);
    const o = G.outputs.slice();
    [o[0], o[5]] = [o[5]!, o[0]!];
    expect(verifyAlignedBit({ ...G, outputs: o }).allPartialOutputsExact).toBe(false);
    const missing = G.totals.slice();
    missing[3] = -1;
    expect(verifyAlignedBit({ ...G, totals: missing }).totalsExact).toBe(false);
  });
  test("bit network formulas: the published h = 50 counts with R = 494196; the role budget is sharp", () => {
    const nw = alignedBitNetwork(50, 494196n);
    expect(eq(nw.eta, q(49n, 1284490000n))).toBe(true);
    const L0 = q(11737n, 1000n);
    const a = q(326n, TEN(11));
    const B = alignedRoleBudget(50, a, L0);
    expect(lt(mul(a, L0), alignedBitNetwork(50, B).eta)).toBe(true);
    expect(lt(mul(a, L0), alignedBitNetwork(50, B + 1n).eta)).toBe(false);
  });
  test("PR 6's parameters satisfy the fast system; kappa = G_* fails", () => {
    const P = pr6Params();
    expect(failingChecks(P)).toEqual([]);
    expect(lt(P.kappa, fastMinimumMargin(P))).toBe(true);
    expect(lt(fastMinimumMargin(P), fastMinimumMargin(P))).toBe(false);
  });
});

describe("PR 4b: retained totals on PR 3's circuit, small ground sets", () => {
  for (const h of [10, 12])
    test(`h = ${h}: base side map exact, every retained total exact and disjoint`, () => {
      const r = analyseRetained(buildComplexCircuit(h, "leftFold", true));
      expect([r.base.sideMapExact, r.totalsExact, r.disjoint, r.distinctTotals, r.totals.length]).toEqual([true, true, true, true, h]);
      expect(r.newAncestors).toBeGreaterThan(0);
      // activated ancestors = all kept additions minus the base circuit's additions
      expect(r.newAncestors).toBe(r.additions - r.base.additions);
    });
  test("a corrupted retention (two totals swapped, or one missing) is rejected", () => {
    const c = buildComplexCircuit(10, "leftFold", true);
    const m = new Map(c.retained!);
    const a = m.get(1 << 0)!;
    m.set(1 << 0, m.get(1 << 1)!);
    m.set(1 << 1, a);
    expect(analyseRetained({ ...c, retained: m }).totalsExact).toBe(false);
    const m2 = new Map(c.retained!);
    m2.delete(0);
    expect(analyseRetained({ ...c, retained: m2 }).totalsExact).toBe(false);
  });
  test("the central scatter identity holds at h = 8, 10 and the doc's network formulas give its stated eta", () => {
    for (const h of [8, 10]) expect(scatterIdentity(h)).toEqual({ ok: true, sumIdentity: true });
    expect(eq(sharedRetainedNetwork(24, 90950n).eta, q(365n, 1285272576n))).toBe(true);
    expect(eq(sharedRetainedNetwork(24, 90951n).eta, q(365n, 1285272576n))).toBe(false);
  });
});
