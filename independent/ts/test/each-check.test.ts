// Every listed inequality has a failure mode: for each named check there is an
// input just past its limit that makes exactly that check (possibly with others)
// fail. Deleting or weakening any listed check therefore breaks a test here or in
// the other suites. Checks that hold for every positive input have no such input;
// they are named at the end and in the README.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, le, eq, ONE, ZERO, type Q } from "../src/rational";
import { noteParams, parameterChecks, holds, type Check, type Params } from "../src/parameters";
import { guardChecks } from "../src/guard";
import { gaussianChecks } from "../src/gaussian";
import { complexNetwork, ground } from "../src/networks";
import { compactParams, compactParameterChecks, compactMarginChecks, compactStatedValues, layerExponents, type CompactParams } from "../src/compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../src/compact/guard";
import { savingEnclosure, minusLogOneMinusEnclosure } from "../src/compact/ceiling";

const names = (ks: Check[]) => ks.filter((k) => !holds(k)).map((k) => k.name);

describe("2^-59 parameter list: each check has a violating input", () => {
  const p = noteParams();
  const f = (o: Partial<Params>) => names(parameterChecks({ ...p, ...o }));
  const cases: [string, Partial<Params>][] = [
    ["tau > 0", { tau: ZERO }],
    ["tau < 1", { tau: ONE }],
    ["sigma > 0", { sigma: ZERO }],
    ["sigma < 1", { sigma: ONE }],
    ["c > 0", { c: ZERO }],
    ["epsilon > 0", { epsilon: ZERO }],
    ["tau < lambda", { lambda: p.tau }],
    ["sigma < lambda", { lambda: p.sigma }],
    ["lambda < 1", { lambda: ONE }],
    ["lambda' < 1", { lambdaPrime: ONE }],
    ["2*epsilon < 1", { epsilon: q(1n, 2n) }],
    ["epsilon(1-tau) < 1-tau", { epsilon: ONE }],
    ["epsilon(1+c) < 1", { epsilon: div(ONE, add(ONE, p.c)) }],
    ["epsilon + delta < 1", { epsilon: sub(ONE, p.delta) }],
    ["delta > 0", { delta: ZERO }],
    ["alpha exponent 1/4+epsilon/4 < 1/2", { epsilon: ONE }],
    ["gamma exponent 1/2+3*epsilon/2 < 1", { epsilon: q(1n, 3n) }],
    ["epsilon*c > 0", { c: ZERO }],
    ["epsilon*c < 1 - epsilon", { c: div(sub(ONE, p.epsilon), p.epsilon) }],
    ["1 - epsilon > 0", { epsilon: ONE }],
    ["g1 > 0", { epsilon: div(ONE, add(ONE, p.c)) }],
    ["g2 > 0", { c: ZERO }],
    ["g3 > 0", { lambdaPrime: ONE }],
    ["g4 > 0", { tau: ONE }],
    ["g5 > 0", { epsilon: mul(q(4n, 5n), sub(q(1n, 4n), p.delta)) }],
    ["g6 > 0", { epsilon: sub(ONE, p.delta) }],
    ["g7 > 0", { epsilon: ZERO }],
    ["kappa > 0", { kappa: ZERO }],
  ];
  for (const [name, o] of cases) test(name, () => expect(f(o)).toContain(name));
});

describe("compact-control parameter and margin lists: each check has a violating input", () => {
  const p = compactParams();
  const f = (o: Partial<CompactParams>) => {
    const r = { ...p, ...o };
    return [...names(compactParameterChecks(r)), ...names(compactMarginChecks(r))];
  };
  const cases: [string, Partial<CompactParams>][] = [
    ["tau > 0", { tau: ZERO }],
    ["tau < 1", { tau: ONE }],
    ["sigma > 0", { sigma: ZERO }],
    ["sigma < 1", { sigma: ONE }],
    ["epsilon > 0", { epsilon: ZERO }],
    ["tau < lambda", { lambda: p.tau }],
    ["lambda' < 1", { lambdaPrime: ONE }],
    ["lambda < 1", { lambda: ONE }],
    ["0 < lambda'", { lambdaPrime: ZERO }],
    ["2*epsilon < 1", { epsilon: q(1n, 2n) }],
    ["epsilon(1-tau) < 1-tau", { epsilon: ONE }],
    ["epsilon(1+c) < 1", { epsilon: div(ONE, add(ONE, p.c)) }],
    ["epsilon + delta < 1", { epsilon: sub(ONE, p.delta) }],
    ["delta > 0", { delta: ZERO }],
    ["alpha exponent 1/4+epsilon/4 < 1/2", { epsilon: ONE }],
    ["gamma exponent 1/2+3*epsilon/2 < 1", { epsilon: q(1n, 3n) }],
    ["epsilon*c > 0", { c: ZERO }],
    ["epsilon*c < 1 - epsilon", { c: div(sub(ONE, p.epsilon), p.epsilon) }],
    ["1 - epsilon > 0", { epsilon: ONE }],
    ["kappa > 0", { kappa: ZERO }],
    ["kappa < g1", { epsilon: div(ONE, add(ONE, p.c)) }],
    ["kappa < g4", { tau: ONE }],
    ["kappa < g5", { delta: q(125n, 10n ** 6n) }],
    ["kappa < g6", { epsilon: sub(ONE, p.delta) }],
    ["kappa < g7", { epsilon: p.kappa }],
  ];
  for (const [name, o] of cases) test(name, () => expect(f(o)).toContain(name));
});

describe("compact-control stated values are pinned by the parameters", () => {
  const p = compactParams();
  const wrong = (o: Partial<CompactParams>) => compactStatedValues({ ...p, ...o }).filter((r) => !r.ok).map((r) => r.name);
  test("epsilon = 1998/10000 changes every epsilon-dependent displayed value", () => {
    expect(wrong({ epsilon: q(1998n, 10000n) })).toEqual([
      "eps C1 = 99872039/10^8",
      "alpha exponent 1/4 + eps/4 = 11999/40000",
      "gamma exponent 1/2 + 3 eps/2 = 15997/20000",
      "prime-interval exponent 1 - 2 eps = 3001/5000",
      "K exponent eps c = 1999/50000",
      "ell exponent 1 - eps = 8001/10000",
      "G_* = 333833/(4*10^15)",
      "G_* - kappa = 1833/(4*10^15)",
    ]);
  });
  test("c = 14/100 changes the reservation exponent and moves the minimum from g3 to g2", () => {
    const w = wrong({ c: q(14n, 100n) });
    for (const n of ["chi_reserve = 1 - c = 4/5", "K exponent eps c = 1999/50000", "G_* = g3"]) expect(w).toContain(n);
  });
});

describe("guards and Gaussian lists: each check with a failure mode has a violating input", () => {
  const cx50 = complexNetwork(50);
  const m50 = ground(50).m;
  const p59 = noteParams();
  test("2^-59 guard: m = 2, s = 1, beta = 89/100", () => {
    expect(names(guardChecks(cx50.W, cx50.s, 2n, p59.beta, p59.C1))).toContain("m >= 3");
    expect(names(guardChecks(cx50.W, 1n, m50, p59.beta, p59.C1))).toContain("s >= 2");
    expect(names(guardChecks(cx50.W, cx50.s, m50, q(89n, 100n), p59.C1))).toContain("5 - 4 beta <= 7/5");
  });
  const cx25 = complexNetwork(25);
  const m25 = ground(25).m;
  const pc = compactParams();
  const g = (o: { m?: bigint; s?: bigint; C1?: Q }) => names(compactGuardChecks(cx25.W, o.s ?? cx25.s, o.m ?? m25, pc.beta, pc.zeta, o.C1 ?? pc.C1));
  test("compact guard: m = 2, s = 1, C1 = 1/2, C1 one unit of 10^-4 above its definition", () => {
    expect(g({ m: 2n })).toContain("m >= 3 (also gives log m > 1)");
    expect(g({ s: 1n })).toContain("s >= 2");
    expect(g({ C1: q(1n, 2n) })).toContain("C1 >= 1 (so 18d <= 18 d^C1)");
    expect(g({ C1: add(pc.C1, q(1n, 10000n)) })).toEqual(["C1 = 5 - 4 beta + zeta (<=)"]);
  });
  test("Gaussian: epsilon = 1/3 breaks gamma = o(p) and the 2^40 cutoff; epsilon = 1 breaks alpha < sqrt p", () => {
    const third = names(gaussianChecks(q(1n, 3n), q(1n), "test"));
    expect(third).toContain("gamma exponent < 1 (gamma = o(p))");
    expect(third.some((n) => n.startsWith("b >= 2^40 gives"))).toBe(true);
    expect(names(gaussianChecks(ONE, q(2n), "test"))).toContain("alpha exponent 1/4 + eps/4 < 1/2 (alpha < sqrt p)");
  });
});

describe("identities and structure of the new recurrence and enclosures", () => {
  test("chi equals tau when sigma <= tau, and the beta-weighted mean of tau and sigma when sigma > tau", () => {
    const p = compactParams();
    const half = q(1n, 2n);
    const lo = { ...p, tau: q(9n, 10n), sigma: q(8n, 10n), beta: half };
    expect(eq(layerExponents(lo).chi, q(9n, 10n))).toBe(true);
    const hi = { ...p, tau: q(8n, 10n), sigma: q(9n, 10n), beta: half };
    expect(eq(layerExponents(hi).chi, q(17n, 20n))).toBe(true); // (8/10 + 9/10)/2
    expect(eq(layerExponents({ ...hi, beta: ZERO }).chi, q(9n, 10n))).toBe(true); // beta -> 0: sigma
  });
  test("the saving enclosure contains x/L for every x in the numerator's and L in the logarithm's enclosure (interval division)", () => {
    const eta = complexNetwork(25).eta;
    const num = minusLogOneMinusEnclosure(eta);
    const e = savingEnclosure(eta, { lower: q(9n), upper: q(10n) });
    expect(le(e.lower, div(num.lower, q(10n))) && le(div(num.upper, q(9n)), e.upper)).toBe(true);
  });
  test("the intermediate bound A <= s(8+E) d^(5-4beta) is checked on its own (B taken huge, s = m^6)", () => {
    const cx = complexNetwork(25);
    const m = ground(25).m;
    const { E } = compactGuardConstants(cx.W, cx.s, m, compactParams().zeta);
    const s = m ** 6n;
    expect(depthSamplesAtPowers([250], m, s, E, s ** 300n, compactParams().beta).ok).toBe(false);
  });
});

// Checked by `bun run check`, but true for every positive input, so no test can make them fail:
//   s(8+E) <= 9B^2 (both guards), 18mB^2 + 18 <= 36mB^2, 9mB^2(1+1/zeta) + 18 <= C0 (given C0's definition),
//   8d + floor(D/2) + 9 <= 18d, and the constants 36 < 128, 184 < 2^8, 8.369598075e-11 < 2^-33.
