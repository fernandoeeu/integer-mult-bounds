// PR re-checks: the full-size runs (h = 50 aligned graph, h = 25 compressed
// circuit, h = 24 rectangle plan). Each heavy computation is done once per
// process (cached in src/prs/rows.ts) and then reused by the failure cases.
import { describe, expect, test } from "bun:test";
import { q, sub, mul, type Q } from "../../src/rational";
import { buildPairedCircuit } from "../../src/circuit";
import { compactMinimumMargin } from "../../src/compact/witness";
import { minimumMargin } from "../../src/parameters";
import { largestGridSaving } from "../../src/ceiling";
import { standardLabelling, mergeWith, pruneMerged, verifyMerged } from "../../src/prs/aligned";
import { buildComplexCircuit, verifyComplexCircuit } from "../../src/prs/complexCircuit";
import { pr2, pr2Params, STATED_PR2 } from "../../src/prs/pr2";
import { pr3, pr3Params, STATED_PR3 } from "../../src/prs/pr3";
import { pr4, pr4Params, STATED_PR4 } from "../../src/prs/pr4";
import { comparePR1, comparePR2, comparePR3, comparePR4, readCert } from "../../src/prs/compare";
import type { Result } from "../../src/prs/rows";

const LONG = 900_000;
const TEN = (k: number) => 10n ** BigInt(k);
const failing = (rs: Result[]) => rs.filter((r) => !r.ok).map((r) => r.name);
const verdictOk = (rs: Result[]) => rs.every((r) => r.ok || r.kind === "observation");
const perturb = (v: unknown): unknown => (typeof v === "bigint" ? v + 1n : typeof v === "number" ? v + 1 : mul(v as Q, q(101n, 100n)));
/**
 * Inputs that are compared only through an inequality with room are moved past their limit
 * instead of by 1%: PR 2's a_c (eta_c > a_c L0 has room up to 1.69/10^11) and PR 4's stated
 * gate count (only "< 12 W" is checked).
 */
const PAST_LIMIT: Record<string, unknown> = { "2.ac": q(2n, TEN(11)), "4.gates": 12n * 3013310215168n };

describe("PR 2: aligned paired circuit at h = 50", () => {
  test("the published claim passes every counted row", () => expect(verdictOk(pr2().results)).toBe(true), LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR2)) {
      const rs = pr2({ stated: { [k]: PAST_LIMIT[`2.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
  const P = pr2Params();
  const cases: [string, any, string[]][] = [
    ["a = 306/10^11 (stated a moved by one grid step)", { stated: { a: q(306n, TEN(11)) } }, ["eta_b > a L0, a = 305/10^11", "R within the role budget for a = 305/10^11"]],
    ["kappa = G", { p: { ...P, kappa: minimumMargin(P) } }, ["kappa < G = min g_j"]],
    ["lambda' = lambda", { p: { ...P, lambdaPrime: P.lambda } }, ["lambda < lambda'"]],
    ["tau = lambda", { p: { ...P, tau: P.lambda } }, ["tau < lambda"]],
    ["beta = 899/1000", { p: { ...P, beta: q(899n, 1000n) } }, ["beta >= 9/10", "5 - 4 beta <= 7/5"]],
  ];
  for (const [label, o, names] of cases)
    test(label, () => {
      const f = failing(pr2(o).results);
      for (const n of names) expect(f).toContain(n);
    }, LONG);
  test("the generalised merge reproduces the published graph with the standard labelling (c = 450394, 40256 merged)", () => {
    const local = buildPairedCircuit(49);
    const { graph, removed } = pruneMerged(mergeWith(local, 50, standardLabelling(50)));
    expect([graph.left.length, graph.mergedAdditions, removed]).toEqual([450394, 40256, 0]);
    expect(verifyMerged(graph).allPartialOutputsExact).toBe(true);
  }, LONG);
});

describe("PR 3: compressed complex circuit at h = 25", () => {
  test("the published claim passes every counted row", () => expect(verdictOk(pr3().results)).toBe(true), LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR3)) {
      const rs = pr3({ stated: { [k]: PAST_LIMIT[`3.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
  const P = pr3Params();
  const cases: [string, any, string[]][] = [
    ["a_c = 15/10^9", { stated: { ac: q(15n, TEN(9)) } }, ["eta_c > a_c (966/100), a_c = 14/10^9"]],
    ["lambda = tau", { p: { ...P, lambda: P.tau } }, ["tau < lambda", "chi < lambda"]],
    ["kappa = G_*", { p: { ...P, kappa: compactMinimumMargin(P) } }, ["kappa < g3"]],
    ["c = 1/5 (g2 binds)", { p: { ...P, c: q(1n, 5n) } }, ["kappa < g2"]],
    ["epsilon = 1/5", { p: { ...P, epsilon: q(1n, 5n) } }, ["3/4 + delta + 5*epsilon/4 < 1"]],
    ["lambda' = 1 - (1-beta)(1-sigma) (leaf boundary)", { p: { ...P, lambdaPrime: sub(q(1n), mul(sub(q(1n), P.beta), sub(q(1n), P.sigma))) } }, ["sigma + beta(1-sigma) < lambda'"]],
    ["C1 = 6 (guard definition; eps C1 > 1)", { p: { ...P, C1: q(6n) } }, ["C1 = 5 - 4 beta + zeta (<=)", "epsilon*C1 < 1"]],
  ];
  for (const [label, o, names] of cases)
    test(label, () => {
      const f = failing(pr3(o).results);
      for (const n of names) expect(f).toContain(n);
    }, LONG);
  test("the other order of the region additions gives the same counts", () => {
    const r = verifyComplexCircuit(buildComplexCircuit(25, "rightFold"));
    expect([r.additions, r.disjointAdditions, r.starAdditions, r.injections, r.sideMapExact]).toEqual([80595, 68595, 12000, 27600, true]);
  }, LONG);
  test("largest complex saving on the 10^-9 grid is 14", () => {
    const eta = pr3().values.network.eta;
    expect(largestGridSaving(eta, q(966n, 100n), TEN(9))).toBe(14n);
  }, LONG);
});

describe("PR 4: retained complex totals at h = 24", () => {
  test("the published claim passes every counted row", () => expect(verdictOk(pr4().results)).toBe(true), LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR4)) {
      const rs = pr4({ stated: { [k]: PAST_LIMIT[`4.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
  const P = pr4Params();
  const cases: [string, any, string[]][] = [
    ["lambda = tau", { p: { ...P, lambda: P.tau } }, ["tau < lambda", "chi < lambda"]],
    ["kappa = G_*", { p: { ...P, kappa: compactMinimumMargin(P) } }, ["kappa < g3"]],
    ["kappa = 2^-31", { p: { ...P, kappa: q(1n, 1n << 31n) } }, ["kappa > 2^-31"]],
    ["c = 0", { p: { ...P, c: q(0n) } }, ["c > 0", "max{1-c,0} < lambda'"]],
    ["a_c = 0 (sigma = 1)", { p: { ...P, sigma: q(1n), ac: q(0n) } }, ["sigma < 1"]],
  ];
  for (const [label, o, names] of cases)
    test(label, () => {
      const f = failing(pr4(o).results);
      for (const n of names) expect(f).toContain(n);
    }, LONG);
  test("largest complex saving on the 10^-11 grid is 752 (the claim 750 holds; 753 would not)", () => {
    expect(largestGridSaving(pr4().values.network.eta, q(477n, 50n), TEN(11))).toBe(752n);
  }, LONG);
});

describe("certificates: field-by-field comparison, and corrupted copies", () => {
  const corrupt = async (name: string, path: string[], value: string) => {
    const c: any = await readCert(name);
    let o = c;
    for (const k of path.slice(0, -1)) o = o[k];
    o[path.at(-1)!] = value;
    return c;
  };
  test("no disagreement with any of the four certificates", async () => {
    for (const f of [comparePR1, comparePR2, comparePR3, comparePR4]) expect((await f(false)).DIFFER).toBe(0);
  }, LONG);
  test("a changed value in each certificate is reported", async () => {
    expect((await comparePR1(false, await corrupt("pr1-paired-tuned-parameters.json", ["witness", "minimum_margin"], "1/2"))).DIFFER).toBe(1);
    expect((await comparePR2(false, await corrupt("pr2-aligned-paired-network.json", ["global_circuit", "additions"], "435451"))).DIFFER).toBe(1);
    expect((await comparePR3(false, await corrupt("pr3-complex-network.json", ["complex_counts", "W"], "1741801270001"))).DIFFER).toBe(1);
    expect((await comparePR4(false, await corrupt("pr4-retained-complex-layer.json", ["main", "counts", "roles"], "365761"))).DIFFER).toBe(1);
  }, LONG);
  test("an extra, unclassified field makes the comparison refuse", async () => {
    const c: any = await readCert("pr3-complex-network.json");
    c.extra = "1";
    expect(comparePR3(false, c)).rejects.toThrow();
  }, LONG);
});

describe("bun run check:prs", () => {
  test("exit 0 for PR 1 as published, exit 1 with kappa moved past G", () => {
    const run = (extra: string[]) => Bun.spawnSync(["bun", "src/prs/main.ts", "--only=1", ...extra], { cwd: `${import.meta.dir}/../..` }).exitCode;
    expect(run([])).toBe(0);
    expect(run(["--set=pr1.kappa=1/100000000000000000"])).toBe(1);
  }, LONG);
});

