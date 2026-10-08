// PR re-checks of 8 October 2026 (later), entries 14 to 16: source frames with data corners
// (PR 14), the smaller h = 30 network with every complex residual batched (PR 15) and the
// nested basis at h = 32 (PR 16). Failure modes: each input just past its limit must make a
// named row (or the underlying function) fail.
import { describe, expect, test } from "bun:test";
import { q, add, sub, lt, ONE, type Q } from "../../src/rational";
import { momentWeights, momentUpperSecond } from "../../src/prs/batched";
import { primeFieldBitNetwork } from "../../src/prs/pr7";
import { pr14, pr14Params, pr14Classes, STATED_PR14 } from "../../src/prs/pr14";
import { pr15, pr15Params, pr15Epsilon, PR15_HISTOGRAM, STATED_PR15 } from "../../src/prs/pr15";
import { pr16, pr16Params, pr16Classes, PR16_LOCAL, pr16Histogram, STATED_PR16 } from "../../src/prs/pr16";
import { convexPathBound, threeHalvesBelow, roundedLogUp, histogramRankSum } from "../../src/prs/allResiduals";
import { bitClasses } from "../../src/prs/batched";

const TEN = (k: number) => 10n ** BigInt(k);
const failing = (rs: { ok: boolean; kind: string; name: string }[]) => rs.filter((r) => !r.ok && r.kind !== "observation").map((r) => r.name);

describe("entries pass as published", () => {
  test("PR 14, 15, 16: no counted row fails", () => {
    expect(failing(pr14().results)).toEqual([]);
    expect(failing(pr15().results)).toEqual([]);
    expect(failing(pr16().results)).toEqual([]);
  }, 120000);
});

describe("PR 14 failure modes", () => {
  test("a_b one step past the grid maximum (1821/10^9) fails both routes", () => {
    const f = failing(pr14({ stated: { a: q(1821n, TEN(9)) }, p: { ...pr14Params(), a: q(1821n, TEN(9)), tau: sub(ONE, q(1821n, TEN(9))) } }).results);
    expect(f.some((n) => n.startsWith("Psi(1 - 1816/10^9)"))).toBe(true);
    expect(f.some((n) => n.startsWith("second route: Psi(1-a_b)"))).toBe(true);
  });
  test("a misstated S or gap claim fails", () => {
    expect(failing(pr14({ stated: { S: STATED_PR14.S + 1n } }).results)).toContain("S = s - B(26880 + 26940) - 2N(25142 + 842 + 782)");
    expect(failing(pr14({ stated: { gapDecimal: q(19155n, TEN(14)) } }).results)).toContain("certified gap > 1.9154*10^-10");
  });
  test("kappa = G_* fails; a complex saving below the leaf limit fails", () => {
    const p = pr14Params();
    const G = pr14().values.G;
    expect(failing(pr14({ p: { ...p, kappa: G } }).results)).toContain("kappa < g3");
    const ac = q(1817n, TEN(9)); // (1 - beta) a_c < a_b
    expect(failing(pr14({ stated: { ac }, p: { ...p, ac, sigma: sub(ONE, ac) } }).results)).toContain("(1 - beta) a_c > a_b (sigma + beta(1 - sigma) < tau)");
  });
  test("role budget: R + 50034 roles no longer certifies 1816/10^9", () => {
    const at = (R: bigint) => {
      const n = primeFieldBitNetwork(30, R);
      return lt(momentUpperSecond(momentWeights(n.m, n.W, n.s, pr14Classes(30n, n.v, R)).items, STATED_PR14.a).bound, ONE);
    };
    expect(at(STATED_PR14.R + 50033n)).toBe(true);
    expect(at(STATED_PR14.R + 50034n)).toBe(false);
  });
  test("the rounded log is an upper bound and rounding down would understate it", () => {
    const r = q(224n, 225n);
    const L = roundedLogUp(r, TEN(10));
    expect(lt(sub(L, q(1n, TEN(10))), L)).toBe(true);
    expect(lt(roundedLogUp(r, TEN(10)), add(roundedLogUp(r, TEN(12)), q(1n, TEN(10))))).toBe(true);
  });
});

describe("PR 15 failure modes", () => {
  test("a_b + 10^-12 fails the conservative bound with own logs", () => {
    const a = add(STATED_PR15.a, q(1n, TEN(12)));
    const f = failing(pr15({ stated: { a }, p: { ...pr15Params(), a, tau: sub(ONE, a) } }).results);
    expect(f.some((n) => n.startsWith("Psi(1 - a_b) <= sum w_i/(1 - a_b l_i) < 1 with this checker's own"))).toBe(true);
  });
  test("R + 162 roles fails the second route (only 161 roles of room)", () => {
    const at = (R: bigint) => {
      const n = primeFieldBitNetwork(30, R);
      return lt(momentUpperSecond(momentWeights(n.m, n.W, n.s, bitClasses(30n, n.v, R, "sourceFrames").classes).items, STATED_PR15.a).bound, ONE);
    };
    expect(at(STATED_PR15.R + 161n)).toBe(true);
    expect(at(STATED_PR15.R + 162n)).toBe(false);
  });
  test("a tampered histogram (one edge moved from rank 2 to rank 3) breaks the rank sum", () => {
    const h = PR15_HISTOGRAM.map(([r, c]) => [r, r === 2n ? c - 1n : r === 3n ? c + 1n : c] as [bigint, bigint]);
    expect(failing(pr15({ histogram: h }).results)).toContain("sum over the histogram of rank x copies = s");
  });
  test("an understated path bound and an off-grid epsilon fail", () => {
    expect(failing(pr15({ stated: { pathUpper: q(27921787004126n, 28n * TEN(12)) } }).results).some((n) => n.startsWith("(M/m)^(3/2)"))).toBe(false); // still above the sharp bound
    const g = convexPathBound(21952n, 28n, 21896n);
    expect(failing(pr15({ stated: { pathUpper: g.sharp } }).results).some((n) => n.startsWith("(M/m)^(3/2)"))).toBe(true);
    const e = add(pr15Epsilon(STATED_PR15.a, q(1n, TEN(10))), q(1n, TEN(12)));
    expect(failing(pr15({ p: { ...pr15Params(), epsilon: e } }).results)).toContain("eps is on the 10^-12 grid and (1 - delta)/(2 + a_b) - eps < 10^-12");
  });
  test("C1 of the rho = 6/5 guard is rejected for the rho = 3/2 guard", () => {
    expect(failing(pr15({ p: { ...pr15Params(), C1: q(11999n, 10000n) } }).results)).toContain("C1 = rho - (rho - 1) beta + zeta with rho = 3/2 (the guard's exponent)");
  });
});

describe("PR 16 failure modes", () => {
  test("a_b = 1970/10^9 fails both routes; without the nested corner 1960/10^9 fails", () => {
    const a = q(1970n, TEN(9));
    const f = failing(pr16({ stated: { a }, p: { ...pr16Params(), a, tau: sub(ONE, a) } }).results);
    expect(f.some((n) => n.startsWith("sum w_i/(1 - a_b l_i) < 1 - 3/10^10"))).toBe(true);
    expect(f).toContain("second route: Psi(1 - a_b) < 1");
    const n = primeFieldBitNetwork(32, STATED_PR16.R);
    expect(lt(momentUpperSecond(momentWeights(n.m, n.W, n.s, pr16Classes(32n, n.v, STATED_PR16.R, false)).items, STATED_PR16.a).bound, ONE)).toBe(false);
  });
  test("a changed local histogram entry breaks both stated sums", () => {
    const save = PR16_LOCAL[26]!;
    PR16_LOCAL[26] = save + 1n;
    try {
      const f = failing(pr16().results);
      expect(f).toContain("sum_r r c_r (local table)");
      expect(f.some((x) => x.startsWith("sum_r r H_r"))).toBe(true);
    } finally {
      PR16_LOCAL[26] = save;
    }
    expect(histogramRankSum(pr16Histogram(3276n, 28n, STATED_PR16.Bc))).toBe(45772350635112192n);
  });
  test("the Taylor and y/9 bounds reject understated values", () => {
    expect(threeHalvesBelow(q(1n, 98n), q(1n, 980n))).toBe(false); // y^(3/2) > y/10
    expect(threeHalvesBelow(q(1n, 98n), q(1n, 882n))).toBe(true); // y/9
    expect(failing(pr16({ stated: { pathBound: q(11005894n, 11035584n) } }).results)).toContain("the sum of the two bounds is exactly 11005895/11035584");
  });
  test("kappa = G_* and a misstated minimum margin fail", () => {
    const G = pr16().values.G;
    expect(failing(pr16({ p: { ...pr16Params(), kappa: G } }).results)).toContain("kappa < g3");
    expect(failing(pr16({ stated: { minMargin: add(STATED_PR16.minMargin, q(1n, TEN(30))) } }).results)).toContain("minimum margin as stated");
  });
  test("a complex saving whose moment fails is rejected (a_c = 5/10^6)", () => {
    const ac = q(5n, TEN(6));
    expect(failing(pr16({ stated: { ac }, p: { ...pr16Params(), ac, sigma: sub(ONE, ac) } }).results).some((n) => n.startsWith("sum H_r r/(Wm(1 - a_c l_r)) < 1"))).toBe(true);
  });
});

// keep the type import used
export type _Q = Q;
