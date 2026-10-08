// PR re-checks: the fast part. Logarithm comparisons against exact integer
// comparisons, PR 1 (parameter-only), small instances of the three circuit
// constructions, and corrupted inputs that the verifiers must reject.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, lt, le, ONE, type Q } from "../../src/rational";
import { floorRoot } from "../../src/intmath";
import { pairedBitNetwork } from "../../src/networks";
import { buildPairedCircuit } from "../../src/circuit";
import { floorTwoPower, lessThanTwoPowerTimes } from "../../src/prs/logs";
import { pr1, pr1Params, recipe, supremumBySqrt, supQuadratic, STATED_PR1 } from "../../src/prs/pr1";
import { alignedLabelling, standardLabelling, labellingIsValid, mergeWith, pruneMerged, verifyMerged, rootPairImages } from "../../src/prs/aligned";
import { buildComplexCircuit, verifyComplexCircuit } from "../../src/prs/complexCircuit";
import { bestPlan, disjointBranch, pairTree, roles, type Plan } from "../../src/prs/retained";
import { minimumMargin } from "../../src/parameters";
import type { Result } from "../../src/prs/rows";

const TEN = (k: number) => 10n ** BigInt(k);
const failing = (rs: Result[]) => rs.filter((r) => !r.ok).map((r) => r.name);
const verdictOk = (rs: Result[]) => rs.every((r) => r.ok || r.kind === "observation");
/** Perturb a stated value: integers by +1, rationals by a factor 101/100. */
const perturb = (v: unknown): unknown => (typeof v === "bigint" ? v + 1n : typeof v === "number" ? v + 1 : mul(v as Q, q(101n, 100n)));

describe("logarithm comparisons agree with exact integer comparisons", () => {
  for (const eps of [q(199n, 1000n), q(1999n, 10000n), q(1n, 3n)])
    test(`floor(2^(k eps)) and gamma < 46 b^e for eps = ${eps.num}/${eps.den}`, () => {
      for (const k of [40, 41, 48, 64, 100]) {
        const exact = floorRoot(1n << (BigInt(k) * eps.num), Number(eps.den));
        expect(floorTwoPower(mul(q(BigInt(k)), eps))).toBe(exact);
        const e = add(q(1n, 2n), mul(q(3n, 2n), eps));
        for (const A of [exact, 46n * exact, 1n << BigInt(Math.floor(k * 0.8))]) {
          const exactLess = A ** e.den < 46n ** e.den * (1n << BigInt(k)) ** e.num;
          expect(lessThanTwoPowerTimes(A, 46n, k, e)).toBe(exactLess);
        }
      }
    });
  test("powers of two are decided exactly: floor(2^8) = 256, floor(2^(8 - 10^-30)) = 255", () => {
    expect(floorTwoPower(q(8n))).toBe(256n);
    expect(floorTwoPower(sub(q(8n), q(1n, TEN(30))))).toBe(255n);
  });
});

describe("PR 1: tuned parameters", () => {
  const base = pr1().results;
  test("the published parameters pass every counted row", () => expect(verdictOk(base)).toBe(true));

  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR1)) {
      const rs = pr1({ stated: { [k]: perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok)]).toEqual([k, true]);
    }
  });

  const P = pr1Params();
  const nudge = (label: string, p: typeof P, expectNames: string[]) =>
    test(label, () => {
      const f = failing(pr1({ p }).results);
      for (const n of expectNames) expect(f).toContain(n);
    });
  // leaf boundary: (1 - beta) b = beta a^2  <=>  beta = b / (b + a^2)
  const betaStar = div(P.ac, add(P.ac, mul(P.a, P.a)));
  nudge("beta at the leaf boundary b/(b + a^2) (recipe recomputed): the leaf condition fails", recipe(P.a, P.ac, betaStar, P.epsilon, P.delta, P.kappa), ["sigma + beta(1-sigma) < lambda'"]);
  test("beta just below the leaf boundary keeps the leaf condition", () => {
    const p = recipe(P.a, P.ac, sub(betaStar, q(1n, TEN(30))), P.epsilon, P.delta, q(1n, TEN(30)));
    expect(failing(pr1({ p }).results)).not.toContain("sigma + beta(1-sigma) < lambda'");
  });
  const epsG5 = mul(sub(q(1n, 4n), P.delta), q(4n, 5n));
  nudge("epsilon at the Gaussian boundary (1/4 - delta) 4/5", recipe(P.a, P.ac, P.beta, epsG5, P.delta, P.kappa), ["3/4 + delta + 5*epsilon/4 < 1"]);
  nudge("delta = 1/4 - 5 eps/4", { ...P, delta: sub(q(1n, 4n), mul(q(5n, 4n), P.epsilon)) }, ["3/4 + delta + 5*epsilon/4 < 1"]);
  nudge("epsilon = 1/5: gamma exponent reaches 4/5", recipe(P.a, P.ac, P.beta, q(1n, 5n), P.delta, P.kappa), ["gamma exponent < 4/5"]);
  nudge("kappa = G", { ...P, kappa: minimumMargin(P) }, ["kappa < G = min g_j"]);
  test("kappa = G - 10^-60 keeps kappa < G (the stated kappa-dependent values then reject it)", () => {
    const f = failing(pr1({ p: { ...P, kappa: sub(minimumMargin(P), q(1n, TEN(60))) } }).results);
    expect(f).not.toContain("kappa < G = min g_j");
    expect(f).toContain("G - kappa = 6.46864326407676563456e-26");
  });
  nudge("beta below 9/10", recipe(P.a, P.ac, q(899n, 1000n), P.epsilon, P.delta, q(1n, TEN(40))), ["5 - 4 beta <= 7/5", "beta >= 9/10"]);
  nudge("C1 = 19/10 - 10^-9", { ...P, C1: sub(q(19n, 10n), q(1n, TEN(9))) }, ["7/5 + 1/2 <= C1"]);
  nudge("C1 = 5 - 4 beta + 1/2", { ...P, C1: add(sub(q(5n), mul(q(4n), P.beta)), q(1n, 2n)) }, ["5 - 4 beta + 1/2 < 2 = C1", "7/5 + 1/2 <= C1"]);
  nudge("C1 = 1/2: epsilon C1 < 1 still holds, the guard rows fail", { ...P, C1: q(1n, 2n) }, ["7/5 + 1/2 <= C1"]);

  test("supremum: the square-root enclosure agrees with 200 exact bisections", () => {
    const { a, ac: b } = P;
    let lo = q(0n);
    let hi = mul(a, a);
    for (let i = 0; i < 200; i++) {
      const mid = div(add(lo, hi), q(2n));
      if (lt(q(0n), supQuadratic(a, b, mid))) lo = mid;
      else hi = mid;
    }
    const s = supremumBySqrt(a, b);
    expect(le(lo, s.z.upper) && le(s.z.lower, hi)).toBe(true);
    expect(lt(minimumMargin(P), s.G.lower)).toBe(true);
  });
  test("supremum: the boxed quadratic equals the crossing of the two capacity bounds", () => {
    // z = (1-beta) b and z (1 - a + a beta) = beta a^2 at the crossing beta_*
    const s = supremumBySqrt(P.a, P.ac, 120);
    const beta = sub(ONE, div(s.z.lower, P.ac));
    const lhs = mul(s.z.lower, add(sub(ONE, P.a), mul(P.a, beta)));
    const rhs = mul(beta, mul(P.a, P.a));
    const rel = div(sub(lhs, rhs), rhs);
    expect(lt(rel.num < 0n ? q(-rel.num, rel.den) : rel, q(1n, TEN(60)))).toBe(true);
  });
});

describe("PR 2: aligned merge on small ground sets", () => {
  for (const h of [8, 10, 12])
    test(`h = ${h}: aligned and standard labellings both verify; root pairs agree only when aligned`, () => {
      const local = buildPairedCircuit(h - 1);
      for (const L of [standardLabelling(h), alignedLabelling(h)]) {
        expect(labellingIsValid(h, L)).toBe(true);
        const { graph, removed } = pruneMerged(mergeWith(local, h, L));
        const r = verifyMerged(graph);
        expect(r.allPartialOutputsExact && r.allAdditionsDisjoint && r.everyNodeHasCommonPoint && r.everyNodeUsed).toBe(true);
        expect(removed).toBe(0);
      }
      expect(rootPairImages(h, alignedLabelling(h)).allGlobalPairs).toBe(true);
      expect(rootPairImages(h, standardLabelling(h)).allGlobalPairs).toBe(false);
    });
  const h = 10;
  const local = buildPairedCircuit(h - 1);
  const G = pruneMerged(mergeWith(local, h, alignedLabelling(h))).graph;
  test("a swapped output pointer is rejected", () => {
    const outputs = G.outputs.slice();
    [outputs[0], outputs[1]] = [outputs[1]!, outputs[0]!];
    expect(verifyMerged({ ...G, outputs }).allPartialOutputsExact).toBe(false);
  });
  test("an addition with a changed operand is rejected", () => {
    const left = G.left.slice();
    left[left.length - 1] = left[0]!;
    const r = verifyMerged({ ...G, left });
    expect(r.allPartialOutputsExact && r.allAdditionsDisjoint && r.everyNodeHasCommonPoint).toBe(false);
  });
  test("a labelling that is not a bijection is rejected", () => {
    const L = alignedLabelling(h).map((o) => o.slice());
    L[3]![0] = L[3]![1]!;
    expect(labellingIsValid(h, L)).toBe(false);
  });
  test("role budget at a = 305/10^11: R = 494347 holds, R = 494348 fails", () => {
    const aL0 = mul(q(305n, TEN(11)), q(11737n, 1000n));
    expect(lt(aL0, pairedBitNetwork(50, 494347n).eta)).toBe(true);
    expect(lt(aL0, pairedBitNetwork(50, 494348n).eta)).toBe(false);
  });
});

describe("PR 3: compressed side circuit on small ground sets", () => {
  for (const h of [9, 12, 14])
    test(`h = ${h}: the side map is exact`, () => {
      const r = verifyComplexCircuit(buildComplexCircuit(h));
      expect(r.sideMapExact && r.allAdditionsDisjoint && r.piecesMeetTargetEvenly).toBe(true);
    });
  const c = buildComplexCircuit(12);
  test("a dropped piece is rejected", () => expect(verifyComplexCircuit({ ...c, pieces: c.pieces.slice(1) }).sideMapExact).toBe(false));
  test("a flipped sign is rejected", () => {
    const pieces = c.pieces.map((p, i) => (i === 5 ? { ...p, sign: (-p.sign) as 1 | -1 } : p));
    expect(verifyComplexCircuit({ ...c, pieces }).sideMapExact).toBe(false);
  });
  test("a duplicated piece is rejected", () => expect(verifyComplexCircuit({ ...c, pieces: [...c.pieces, c.pieces[0]!] }).sideMapExact).toBe(false));
  test("a piece sent to the wrong target is rejected", () => {
    const pieces = c.pieces.map((p, i) => (i === 0 ? { ...p, target: (p.target + 1) % 220 } : p));
    expect(verifyComplexCircuit({ ...c, pieces }).sideMapExact).toBe(false);
  });
});

describe("PR 4: rectangle plans and fixed-pair trees", () => {
  test("the plan's rectangles partition the disjoint pairs exactly (n = 10, 12, 14)", () => {
    for (const n of [10, 12, 14]) expect(disjointBranch(n, bestPlan(n, 3, 3)).exactPartition).toBe(true);
  });
  test("a plan with one product term removed is rejected", () => {
    const p = bestPlan(12, 3, 3);
    const broken: Plan = p.kind === "split" ? { ...p, terms: p.terms!.slice(1) } : { ...p, kind: "empty" };
    expect(disjointBranch(12, broken).exactPartition).toBe(false);
  });
  test("roles = sum (a + b - 1) over the enumerated rectangles", () => {
    for (const n of [10, 12, 14]) {
      const p = bestPlan(n, 3, 3);
      expect(disjointBranch(n, p).rawRoles).toBe(roles(p));
    }
  });
  test("pair trees: sum of leaf depths = n(n-1) - sum_internal (n - |K|), n = 2..60, both splits", () => {
    for (let n = 2; n <= 60; n++)
      for (const s of ["floor", "ceil"] as const) {
        const t = pairTree(n, s);
        expect(t.outputs).toBe(t.formula);
        expect(t.additions).toBe(n - 1);
      }
  });
});

