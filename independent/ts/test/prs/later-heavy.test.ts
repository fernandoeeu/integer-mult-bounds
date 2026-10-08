// PR re-checks of 8 October 2026: the full-size runs (PR 4b at h = 24, PR 5 with the
// h = 25 compressed circuit, PR 6's aligned bit circuit at h = 50). Each heavy
// computation is done once per process (cached in src/prs/rows.ts) and then reused.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, type Q } from "../../src/rational";
import { compactMinimumMargin } from "../../src/compact/witness";
import { pr4b, pr4bParams, STATED_PR4B } from "../../src/prs/pr4b";
import { pr5, pr5Params, STATED_PR5 } from "../../src/prs/pr5";
import { pr6, pr6Params, STATED_PR6 } from "../../src/prs/pr6";
import { fastMinimumMargin, guardBetaThreshold } from "../../src/prs/fastGaussian";
import { comparePR4b, comparePR5, comparePR6, readCert } from "../../src/prs/compare";
import type { Result } from "../../src/prs/rows";

const LONG = 900_000;
const TEN = (k: number) => 10n ** BigInt(k);
const failing = (rs: Result[]) => rs.filter((r) => !r.ok && r.kind !== "observation").map((r) => r.name);
const verdictOk = (rs: Result[]) => rs.every((r) => r.ok || r.kind === "observation");
const perturb = (v: unknown): unknown => (typeof v === "bigint" ? v + 1n : typeof v === "number" ? v + 1 : mul(v as Q, q(101n, 100n)));
/**
 * Stated values compared only through an inequality with room are moved past their limit instead
 * of by 1%: PR 4b's log bound 477/50 (log m < L0 has room; the deficit slack equality still rejects 1%),
 * PR 6's log bound likewise.
 */
const PAST_LIMIT: Record<string, unknown> = { "6.L0": q(11736n, 1000n) };

const cases = (label: string, run: (o: any) => { results: Result[] }, P: any, rows: [string, any, string[]][]) =>
  describe(label, () => {
    for (const [name, o, names] of rows)
      test(name, () => {
        const f = failing(run(o).results);
        for (const n of names) expect(f).toContain(n);
      }, LONG);
  });

describe("PR 4b (head 8c225e6): PR 3's circuit with retained totals at h = 24", () => {
  test("the published claim passes every counted row", () => expect(verdictOk(pr4b().results)).toBe(true), LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR4B)) {
      const rs = pr4b({ stated: { [k]: PAST_LIMIT[`4b.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
});
const P4b = pr4bParams();
cases("PR 4b: parameters past their limits", pr4b, P4b, [
  ["a_c = 2977/10^11 (beyond the certified 2976)", { stated: { ac: q(2977n, TEN(11)) } }, ["eta > a_c (477/50), a_c = 2970/10^11", "eta - (2970/10^11)(477/50) = 406952569/627574500000000000"]],
  ["1 - sigma = 2971/10^11 > the stated a_c", { p: { ...P4b, sigma: sub(q(1n), q(2971n, TEN(11))) } }, ["1 - sigma <= a_c"]],
  ["kappa = G_*", { p: { ...P4b, kappa: compactMinimumMargin(P4b) } }, ["kappa < g3"]],
  ["lambda' = lambda", { p: { ...P4b, lambdaPrime: P4b.lambda } }, ["lambda < lambda'"]],
]);

describe("PR 5: fast Gaussian resampling", () => {
  test("the published claim passes every counted row; exactly the two errata are false observations", () => {
    const rs = pr5().results;
    expect(verdictOk(rs)).toBe(true);
    expect(rs.filter((r) => !r.ok).map((r) => r.name.slice(0, 7))).toEqual(["ERRATUM", "ERRATUM"]);
  }, LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR5)) {
      const rs = pr5({ stated: { [k]: PAST_LIMIT[`5.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
});
const P5 = pr5Params();
const thr5 = guardBetaThreshold(P5);
cases("PR 5: parameters past their limits", pr5, P5, [
  ["kappa = G_*", { p: { ...P5, kappa: fastMinimumMargin(P5) } }, ["kappa < g3"]],
  ["2 eps + delta = 1", { p: { ...P5, epsilon: div(sub(q(1n), P5.delta), q(2n)) } }, ["2*epsilon + delta < 1"]],
  ["beta at the guard threshold, C1 recomputed", { p: { ...P5, beta: thr5, C1: sub(add(q(5n), P5.zeta), mul(q(4n), thr5)) } }, ["epsilon*C1 < 1"]],
  ["lambda' at the leaf boundary", { p: { ...P5, lambdaPrime: sub(q(1n), mul(sub(q(1n), P5.beta), sub(q(1n), P5.sigma))) } }, ["sigma + beta(1-sigma) < lambda'"]],
  ["beta = 3/4 (C1 recomputed): the guard fails", { p: { ...P5, beta: q(3n, 4n), C1: sub(add(q(5n), P5.zeta), q(3n)) } }, ["epsilon*C1 < 1", "beta > (5 + zeta - 1/eps)/4 (the guard threshold)"]],
  ["kappa = 2^-29", { p: { ...P5, kappa: q(1n, 1n << 29n) } }, ["kappa < 2^-29"]],
  ["a_c = 418/10^12 (the earlier complex saving)", { p: { ...P5, ac: q(418n, TEN(12)), sigma: sub(q(1n), q(418n, TEN(12))) } }, ["sigma + beta(1-sigma) < lambda'", "with a_c = 14/10^9 such a beta exists"]],
]);

describe("PR 6: aligned bit circuit with cheaper centers at h = 50", () => {
  test("the published claim passes every counted row; exactly the two errata are false observations", () => {
    const rs = pr6().results;
    expect(verdictOk(rs)).toBe(true);
    expect(rs.filter((r) => !r.ok).map((r) => r.name.slice(0, 7))).toEqual(["ERRATUM", "ERRATUM"]);
  }, LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR6)) {
      const rs = pr6({ stated: { [k]: PAST_LIMIT[`6.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
});
const P6 = pr6Params();
cases("PR 6: parameters past their limits", pr6, P6, [
  ["a = 326/10^11 (one grid step above the certified 325)", { stated: { a: q(326n, TEN(11)) } }, ["eta_b > (325/10^11)(11737/1000)"]],
  ["1 - tau = 326/10^11", { p: { ...P6, tau: sub(q(1n), q(326n, TEN(11))) } }, ["1 - tau <= a = 325/10^11"]],
  ["kappa = G_*", { p: { ...P6, kappa: fastMinimumMargin(P6) } }, ["kappa < g3"]],
  ["lambda' at the leaf boundary", { p: { ...P6, lambdaPrime: sub(q(1n), mul(sub(q(1n), P6.beta), sub(q(1n), P6.sigma))) } }, ["sigma + beta(1-sigma) < lambda'"]],
]);

describe("bun run compare:prs (PRs 4b, 5, 6)", () => {
  const corrupt = async (name: string, path: (string | number)[], value: string) => {
    const c: any = await readCert(name);
    let o = c;
    for (const k of path.slice(0, -1)) o = o[k];
    o[path.at(-1)!] = value;
    return c;
  };
  test("no disagreement with any of the three certificates", async () => {
    for (const f of [comparePR4b, comparePR5, comparePR6]) expect((await f(false)).DIFFER).toBe(0);
  }, LONG);
  test("a changed value in each certificate is reported", async () => {
    expect((await comparePR4b(false, await corrupt("pr4b-retained-complex-layer.json", ["main", "counts", "new_ancestors"], "121"))).DIFFER).toBe(1);
    expect((await comparePR5(false, await corrupt("pr5-fast-gaussian.json", ["neumann_samples", 1, "n_new"], "1024"))).DIFFER).toBe(1);
    expect((await comparePR5(false, await corrupt("pr5-fast-gaussian.json", ["witness", "margins", "g5"], "1/4"))).DIFFER).toBe(1);
    expect((await comparePR6(false, await corrupt("pr6-aligned-bit-network.json", ["circuit", "additions"], "435344"))).DIFFER).toBe(1);
  }, LONG);
  test("an extra, unclassified field makes the comparison refuse", async () => {
    const c: any = await readCert("pr5-fast-gaussian.json");
    c.extra = "1";
    expect(comparePR5(false, c)).rejects.toThrow();
  }, LONG);
});

describe("bun run check:prs (new entries)", () => {
  test("exit 0 for PR 4b as published; exit 1 for PR 5 with kappa moved to G_*", () => {
    const run = (extra: string[]) => Bun.spawnSync(["bun", "src/prs/main.ts", ...extra], { cwd: `${import.meta.dir}/../..` }).exitCode;
    expect(run(["--only=4b"])).toBe(0);
    expect(run(["--only=5", "--set=pr5.kappa=147947041/100000000000000000"])).toBe(1);
  }, LONG);
});
