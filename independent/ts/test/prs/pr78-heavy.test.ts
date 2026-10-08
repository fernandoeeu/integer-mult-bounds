// PR re-checks of 8 October 2026, later entries: the full-size runs of PR 7 (global
// producer at h = 28, about a minute and 1.8 GB once per process) and PR 8, their
// misstated values and parameters past their limits, and corrupted certificates.
import { describe, expect, test } from "bun:test";
import { q, sub, mul, type Q } from "../../src/rational";
import { pr7, pr7Params, STATED_PR7 } from "../../src/prs/pr7";
import { pr8, pr8Params, STATED_PR8 } from "../../src/prs/pr8";
import { fastMinimumMargin } from "../../src/prs/fastGaussian";
import { compactMinimumMargin } from "../../src/compact/witness";
import { comparePR7, comparePR8, readCert } from "../../src/prs/compare";
import type { Result } from "../../src/prs/rows";

const LONG = 1_200_000;
const TEN = (k: number) => 10n ** BigInt(k);
const failing = (rs: Result[]) => rs.filter((r) => !r.ok && r.kind !== "observation").map((r) => r.name);
const verdictOk = (rs: Result[]) => rs.every((r) => r.ok || r.kind === "observation");
const perturb = (v: unknown): unknown =>
  typeof v === "bigint" ? v + 1n : typeof v === "number" ? v + 1 : typeof v === "string" ? v + "9" : mul(v as Q, q(101n, 100n));
/** Values compared only through an inequality with more than 1% room are moved past their limit instead. */
const PAST_LIMIT: Record<string, unknown> = {
  "7.ac": q(395n, TEN(10)), // a_c* = 3.9404e-8
  "7.L0c": q(999n, 100n), // log 21952 = 9.9966
  "8.ac": q(406n, TEN(11)), // a_c* = 4.0579e-9
};

describe("PR 7 at full size", () => {
  test("the published claim passes every counted row", () => expect(verdictOk(pr7().results)).toBe(true), LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR7)) {
      const rs = pr7({ stated: { [k]: PAST_LIMIT[`7.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
  const P = pr7Params();
  const cases: [string, any, string[]][] = [
    ["a = 7502/10^12 (above eta_b / L0 = 7.50197e-9) is not certified", { stated: { a: q(7502n, TEN(12)) } }, ["eta_b > a (9997/1000), a = 3/(4*10^8)"]],
    ["R one role larger than the budget would fail: stated R misread as 11844079", { stated: { R: 11844079n } }, ["R = c + q"]],
    ["kappa = G_*", { p: { ...P, kappa: fastMinimumMargin(P) } }, ["kappa < g3"]],
    ["kappa = 2^-28", { p: { ...P, kappa: q(1n, 2n ** 28n) } }, ["kappa > 2^-28"]],
    ["1 - sigma above a_c", { p: { ...P, sigma: sub(q(1n), q(40n, TEN(9))) } }, ["1 - sigma <= a_c"]],
  ];
  for (const [name, o, names] of cases)
    test(name, () => {
      const f = failing(pr7(o).results);
      for (const n of names) expect(f).toContain(n);
    }, LONG);
  test("the comparison with the certificate has no disagreement, and a changed value is caught", async () => {
    expect((await comparePR7(false)).DIFFER).toBe(0);
    const cert = (await readCert("pr7-prime-field28.json")) as any;
    cert.producer.independent_template_check.new_star_additions = "2623059";
    cert.witness.bit.eta = "39/520019361";
    expect((await comparePR7(false, cert)).DIFFER).toBe(2);
  }, LONG);
});

describe("PR 8 at full size", () => {
  test("the published claim passes every counted row", () => expect(verdictOk(pr8().results)).toBe(true), LONG);
  test("every stated number, misstated, is rejected", () => {
    for (const [k, v] of Object.entries(STATED_PR8)) {
      const rs = pr8({ stated: { [k]: PAST_LIMIT[`8.${k}`] ?? perturb(v) } as any }).results;
      expect([k, rs.some((r) => !r.ok && r.kind !== "observation")]).toEqual([k, true]);
    }
  }, LONG);
  const P = pr8Params();
  const cases: [string, any, string[]][] = [
    ["kappa = G_*", { p: { ...P, kappa: compactMinimumMargin(P) } }, ["kappa < g3"]],
    ["c = 0", { p: { ...P, c: q(0n) } }, ["c > 0"]],
    ["lambda' = 1 - 3996/10^12 (the leaf exponent)", { p: { ...P, lambdaPrime: sub(q(1n), q(3996n, TEN(12))) } }, ["sigma + beta(1-sigma) < lambda'"]],
  ];
  for (const [name, o, names] of cases)
    test(name, () => {
      const f = failing(pr8(o).results);
      for (const n of names) expect(f).toContain(n);
    }, LONG);
  test("the comparison with the certificate has no disagreement, and a changed value is caught", async () => {
    expect((await comparePR8(false)).DIFFER).toBe(0);
    const cert = (await readCert("pr8-geometric-certificate.json")) as any;
    cert.disjoint.additions = "212736";
    cert.physical_phase_audit.invocations[0].rank_sum = "63451";
    expect((await comparePR8(false, cert)).DIFFER).toBe(2);
  }, LONG);
});
