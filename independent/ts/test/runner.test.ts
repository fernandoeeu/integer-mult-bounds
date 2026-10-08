// The rows that `bun run check` prints and counts, tested where they are produced
// (src/checks.ts), not only in the helper functions behind them.
//
// For every counted row (recomputed check, parameter condition, constant, lemma sample)
// there is either
//   - a case below that feeds the runner a misstated note value, a parameter moved past
//     its limit, a different ground size, or a corrupted verifier report, and expects
//     exactly that row (by name) among the failures; or
//   - an entry in NOT_RUNNER_FAILABLE: rows whose inputs the runner never exposes
//     (for example m >= 3 for m = 125000). Each entry names the test in another file
//     that makes the underlying function fail.
// The last tests check that this classification is complete, so a row that is deleted,
// renamed or weakened at its boundary breaks a test here.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, twoPow, show, ONE, ZERO, type Q } from "../src/rational";
import {
  bitRows,
  paired59,
  compact,
  isCounted,
  STATED_BIT,
  STATED_59,
  STATED_COMPACT,
  type Result,
  type BitValues,
} from "../src/checks";
import { noteParams, minimumMargin, type Params } from "../src/parameters";
import { compactParams, layerExponents, compactMinimumMargin, type CompactParams } from "../src/compact/witness";
import { pairedBitNetwork } from "../src/networks";
import { maxSideRoles } from "../src/ceiling";
import { bitValues } from "./shared";

type Group = "bit" | "59" | "compact";
type Case = { group: Group; label: string; expect: string[]; run: () => Result[] };

const TEN = (k: number) => 10n ** BigInt(k);
const failures = (rs: Result[]) => rs.filter((r) => !r.ok).map((r) => r.name);
const fmt = (x: unknown) => (typeof x === "object" && x !== null && "num" in x ? show(x as Q) : String(x));

// ------------------------------------------------------------------ runners with one change
const runBit = (o: { stated?: Partial<typeof STATED_BIT>; v?: BitValues } = {}) => bitRows(o.v ?? bitValues(), { ...STATED_BIT, ...o.stated });
const run59 = (o: { p?: Partial<Params>; stated?: Partial<typeof STATED_59>; h?: number; bit?: BitValues } = {}) =>
  paired59(o.bit ?? bitValues(), { p: { ...noteParams(), ...o.p }, stated: o.stated, h: o.h }).results;
const runCompact = (o: { p?: Partial<CompactParams>; stated?: Partial<typeof STATED_COMPACT>; h?: number } = {}) =>
  compact(undefined, { p: { ...compactParams(), ...o.p }, stated: o.stated, h: o.h }).results;

const P59 = noteParams();
const PC = compactParams();
/** compact parameters with C1 recomputed as 5 - 4 beta + zeta, as the guard note defines it */
const withGuard = (o: Partial<CompactParams>): Partial<CompactParams> => {
  const p = { ...PC, ...o };
  return { ...o, C1: add(sub(q(5n), mul(q(4n), p.beta)), p.zeta) };
};
const savings = (a: Q, ac: Q): Partial<CompactParams> => ({ a, ac, tau: sub(ONE, a), sigma: sub(ONE, ac) });

const cases: Case[] = [];
const add_ = (group: Group, label: string, expectNames: string | string[], run: () => Result[]) =>
  cases.push({ group, label, expect: Array.isArray(expectNames) ? expectNames : [expectNames], run });

// ------------------------------------------------------------------ bit network (B1, B2)
// A misstated displayed value: the recomputed value no longer matches it.
const bitStated: [keyof typeof STATED_BIT, unknown, string[]][] = [
  ["localAdditions", 9812n, ["local additions at n=49"]],
  ["localNonzero", 1271255n, ["local nonzero coefficients"]],
  ["c", 450393n, ["global additions c at h=50"]],
  ["merged", 40257n, ["merged additions"]],
  ["v", 19601n, ["v = C(50,3)"]],
  ["N", 7529536000001n, ["N = v^3"]],
  ["m", 125001n, ["m = h^3"]],
  ["I", 1152480001n, ["I = 3 v^2"]],
  ["zb", 3242n, ["z_b = 3 C(47,2)"]],
  ["Wb", 73269972440000001n, ["original W_b"]],
  ["sb", 9158746553232864000001n, ["original s_b"]],
  ["LbOverN", q(76n, 196n), ["L_b / N"]],
  ["Wpair", 406321422080001n, ["W_b^pair = 2N + 2v^2(R+h)"]],
  ["spair", 50790175992864000001n, ["s_b^pair = W m - N + 6 v^2 h^2"]],
  ["deficitPair", 1767136000001n, ["W m - s > 0 (bit deficit)"]],
  ["etaPair", q(23n, 661055001n), ["eta_b^pair"]],
  ["log2Power", 17n, ["m = 2^16 * x with 1 <= x < 2"]],
  // log 125000 = 11.7360...: the stated bound 11737/1000 cannot be lowered by 1/1000
  ["L0", q(11736n, 1000n), ["e^L0 > m (Taylor partial sum, independent second route)", "log m < L0 = 11737/1000"]],
  ["aB", q(297n, TEN(11)), ["eta_b^pair > a_b L0, a_b = 296/10^11"]],
  ["eigenvalue", q(-40n, 9n), ["exceptional eigenvalue 1 - h/9 = -41/9"]],
];
for (const [key, value, names] of bitStated) add_("bit", `stated ${key} = ${fmt(value)}`, names, () => runBit({ stated: { [key]: value } }));

// A verifier report with one flag false (the verifiers themselves are fed corrupted
// circuits, graphs and matchings in circuit.test.ts).
const flag = (path: "localReport" | "globalReport" | "match", field: string, value: unknown = false): BitValues => {
  const v = bitValues();
  return { ...v, [path]: { ...(v[path] as object), [field]: value } } as BitValues;
};
const bitFlags: [Parameters<typeof flag>[0], string, unknown, string][] = [
  ["localReport", "allAdditionsDisjoint", false, "every local addition joins disjoint supports"],
  ["localReport", "allOutputSupportsExact", false, "every local output support equals its definition (coefficients and zeros)"],
  ["localReport", "everyAdditionUsed", false, "no unused local node"],
  ["globalReport", "everyNodeUsed", false, "every global node has an outgoing use"],
  ["globalReport", "allAdditionsDisjoint", false, "every global addition joins disjoint supports"],
  ["globalReport", "everyNodeHasCommonPoint", false, "every node's triples share a common point (U_z nondegenerate)"],
  ["globalReport", "allPartialOutputsExact", false, "every partial output is exact (recomputed through merged decompositions)"],
  ["match", "bijective", false, "pi is a bijection of the 19600 triples"],
  ["match", "triples", 19599, "pi is a bijection of the 19600 triples"],
  ["match", "intersectionOne", false, "|A cap pi(A)| = 1 for every triple"],
  ["match", "joiningLabelsNested", false, "<t_A, t_pi(A)> = 0 in I - J/9, hence E within H"],
];
for (const [path, field, value, name] of bitFlags) add_("bit", `${path}.${field} = ${value}`, name, () => runBit({ v: flag(path, field, value) }));

// ------------------------------------------------------------------ preserved 2^-59 witness
const s59: [keyof typeof STATED_59, unknown, string[]][] = [
  ["zc", 16357n, ["z_c = C(47,3) + 3*47"]],
  ["Wc", 369474390296480001n, ["W_c"]],
  ["sc", 46184298777878576000001n, ["s_c"]],
  ["LcOverN", q(154n, 392n), ["L_c / N"]],
  ["etaC", q(239n, 1202215191251n), ["eta_c"]],
  ["G", q(272158570n, 156250000000000000000000000n), ["G = min g_j"]],
  ["gammaExponent", q(1596n, 2000n), ["gamma exponent 1/2 + 3 eps/2 <= the stated exponent"]],
  ["gammaExponent", q(1598n, 2000n), ["gamma exponent 1/2 + 3 eps/2 >= the stated exponent"]],
  ["gridBit", 297n, ["largest bit saving on the 10^-11 grid"]],
  ["gridComplex", 2n, ["largest complex saving on the 10^-11 grid"]],
  ["widthConstant", 45n, ["(8*sqrt(32))^2 = 2048 < C^2 for the constant C of eq:gamma"]],
];
for (const [key, value, names] of s59) add_("59", `stated ${key} = ${fmt(value)}`, names, () => run59({ stated: { [key]: value } }));

const a59 = P59.a;
const p59: [string, Partial<Params>][] = [
  ["eta_c > a_c L0, a_c = 1/10^11", { ac: q(2n, TEN(11)) }],
  ["1 - tau <= a_b = 296/10^11 (bit saving certified in B2)", { tau: sub(ONE, q(297n, TEN(11))) }],
  ["tau > 0", { tau: ZERO }],
  ["tau < 1", { tau: ONE }],
  ["sigma > 0", { sigma: ZERO }],
  ["sigma < 1", { sigma: ONE }],
  ["beta >= 9/10", { beta: q(899n, 1000n) }],
  ["beta < 1", { beta: ONE }],
  ["c > 0", { c: ZERO }],
  ["epsilon > 0", { epsilon: ZERO }],
  ["tau < lambda", { lambda: P59.tau }],
  ["sigma < lambda", { lambda: P59.sigma }],
  ["tau(1+c/beta) < lambda", { lambda: sub(ONE, mul(a59, a59)) }],
  ["lambda < lambda'", { lambdaPrime: P59.lambda }],
  ["sigma + beta(1-sigma) < lambda'", { lambdaPrime: sub(ONE, mul(sub(ONE, P59.beta), sub(ONE, P59.sigma))) }],
  ["lambda' < 1", { lambdaPrime: ONE }],
  ["epsilon*C1 < 1", { C1: div(ONE, P59.epsilon) }],
  ["epsilon < 1/3", { epsilon: q(1n, 3n) }],
  ["2*epsilon < 1", { epsilon: q(1n, 2n) }],
  ["epsilon(1-tau) < 1-tau", { epsilon: ONE }],
  ["3/4 + delta + 5*epsilon/4 < 1", { epsilon: mul(q(4n, 5n), sub(q(1n, 4n), P59.delta)) }],
  // nudges move c or delta rather than epsilon where possible: the Gaussian instances
  // evaluate b^epsilon exactly, which is slow for an epsilon with a large denominator
  ["epsilon(1+c) < 1", { c: div(sub(ONE, P59.epsilon), P59.epsilon) }],
  ["epsilon + delta < 1", { delta: sub(ONE, P59.epsilon) }],
  ["delta > 0", { delta: ZERO }],
  ["delta < 1/8", { delta: q(1n, 8n) }],
  ["alpha exponent 1/4+epsilon/4 < 1/2", { epsilon: ONE }],
  ["gamma exponent 1/2+3*epsilon/2 < 1", { epsilon: q(1n, 3n) }],
  ["epsilon*c > 0", { c: ZERO }],
  ["epsilon*c < 1 - epsilon", { c: div(sub(ONE, P59.epsilon), P59.epsilon) }],
  ["1 - epsilon > 0", { epsilon: ONE }],
  ["kappa > 0", { kappa: ZERO }],
  ["kappa < G = min g_j", { kappa: minimumMargin(P59) }],
  // g3 = eps(1 - lambda') raised above g2, so G = g2 = eps beta a^2 but G != g3
  ["G = g2 = g3 = eps beta a^2", { lambdaPrime: sub(ONE, mul(q(2n), mul(P59.beta, mul(a59, a59)))) }],
  // G tripled: then G >= 2 * 2^-59
  ["G < 2 * 2^-59 (so the old half-margin rule is NOT met)", { c: mul(q(3n), P59.c), lambdaPrime: sub(ONE, mul(q(3n), mul(P59.beta, mul(a59, a59)))) }],
  ["5 - 4 beta <= 7/5", { beta: q(899n, 1000n) }],
  ["7/5 + 1/2 <= C1", { C1: q(189n, 100n) }],
  ["b >= 2^40 gives 46 b^e <= b/4 (e = 1/2 + 3 eps/2 = u/v): 184^v <= 2^(40(v-u))", { epsilon: q(1n, 3n) }],
  ...[40, 41, 48, 64, 100].map((e) => [`b = 2^${e}: alpha, gamma meet every stated bound`, { epsilon: q(1n, 3n) }] as [string, Partial<Params>]),
];
for (const [name, p] of p59) add_("59", `parameters for ${name}`, name, () => run59({ p }));

// The complex network at h = 7 has L_c / N = 24/5 > 1/2.
add_("59", "complex network at h = 7", "L_b < N/2 and L_c < N/2", () => run59({ h: 7 }));
// No side-role saving at all (R = 0): the supremal a, hence the fixed-network ceiling, grows past 2^-58.
add_("59", "bit network with R = 0", "fixed-network ceiling a^2/(5(1-a)) < 2^-58", () => run59({ bit: { ...bitValues(), pairedBit: pairedBitNetwork(50, 0n) } }));
// One side role beyond the budget for a_b = 296/10^11.
add_("59", "R one above the role budget", "R is within the role budget for the witness's a_b", () =>
  run59({ bit: { ...bitValues(), R: maxSideRoles(50, P59.a, STATED_BIT.L0) + 1n } }),
);

// ------------------------------------------------------------------ current compact-control witness
const sC: [keyof typeof STATED_COMPACT, unknown, string[]][] = [
  ["m", 15626n, ["m_c = 25^3"]],
  ["v", 2301n, ["v_c = C(25,3)"]],
  ["N", 12167000001n, ["N_c = v_c^3"]],
  ["z", 1607n, ["z_c = C(22,3) + 66"]],
  ["W", 58645352620001n, ["W_c = 2 v^3 + 3 v^2 (v z_c + 26)"]],
  ["L", 10315500001n, ["L_c = 3 v^2 * 25 * 26"]],
  ["s", 916333630984500001n, ["s_c = W_c m_c - 2 N_c + 2 L_c"]],
  ["eta", q(14n, 3464399376n), ["eta_c = (W_c m_c - s_c)/(W_c m_c)"]],
  // log 15625 = 9.6566...: 966/100 cannot be lowered to 965/100
  ["L0c", q(965n, 100n), ["e^(966/100) > m_c (Taylor partial sum, independent second route)", "log m_c < 966/100 (atanh enclosure, 24 terms)"]],
  ["approxSaving", q(41847990373n, TEN(20)), ["actual saving is approximately 4.1847990372e-10 (the whole enclosure rounds to it)"]],
  ["ceilingDecimal", q(8369598074n, TEN(20)), ["a*/5 <= upper/5 < 8.369598075e-11 (stated decimal)"]],
  ["ceilingDecimal", twoPow(-33), ["8.369598075e-11 < 2^-33"]],
  ["witnessFraction", q(1n), ["witness exceeds 99% of the upper enclosure: kappa > (99/100) upper/5"]],
  ["improvement", 47846243n, ["floor(kappa * 2^59) (improvement over the published 2^-59)"]],
  ["widthConstant", 45n, ["(8*sqrt(32))^2 = 2048 < C^2 for the constant C of eq:gamma"]],
];
for (const [key, value, names] of sC) add_("compact", `stated ${key} = ${fmt(value)}`, names, () => runCompact({ stated: { [key]: value } }));

// epsilon = 1988/10000 lowers g3 = eps(1 - lambda') to 8.2999.../10^11 < kappa (1998/10000 would not)
const eps1988 = q(1988n, 10000n);
const pC: [string | string[], Partial<CompactParams>][] = [
  [["eta_c > a_c (966/100), a_c = 418/10^12", "a_c < lower enclosure of the actual saving a* = -log(1-eta_c)/log m_c (second route: Mercator series)"], savings(PC.a, q(419n, TEN(12)))],
  ["1 - tau <= a_b = 296/10^11 (bit saving certified in B2)", savings(q(297n, TEN(11)), PC.ac)],
  ["tau > 0", { tau: ZERO }],
  ["tau < 1", { tau: ONE }],
  ["sigma > 0", { sigma: ZERO }],
  ["sigma < 1", { sigma: ONE }],
  ["beta > 0", withGuard({ beta: ZERO })],
  ["beta < 1", withGuard({ beta: ONE })],
  ["zeta > 0", withGuard({ zeta: q(-1n, 10000n) })],
  [["c > 0", "max{1-c,0} < lambda'"], { c: ZERO }],
  ["epsilon > 0", { epsilon: ZERO }],
  ["tau < lambda", { lambda: PC.tau }],
  ["sigma < lambda", { lambda: PC.sigma }],
  ["chi < lambda", { lambda: layerExponents(PC).chi }],
  ["lambda < lambda'", { lambda: PC.lambdaPrime }],
  ["lambda' < 1", { lambdaPrime: ONE }],
  ["sigma + beta(1-sigma) < lambda'", { lambdaPrime: layerExponents(PC).leaf }],
  ["epsilon*C1 < 1", withGuard({ zeta: q(7n, 1000n) })],
  ["epsilon < 1/3", { epsilon: q(1n, 3n) }],
  ["2*epsilon < 1", { epsilon: q(1n, 2n) }],
  ["epsilon(1-tau) < 1-tau", { epsilon: ONE }],
  [["3/4 + delta + 5*epsilon/4 < 1", "kappa < g5"], { delta: q(125n, TEN(6)) }],
  [["epsilon(1+c) < 1", "kappa < g1"], { c: div(sub(ONE, PC.epsilon), PC.epsilon) }],
  [["epsilon + delta < 1", "kappa < g6"], { delta: sub(ONE, PC.epsilon) }],
  ["delta > 0", { delta: ZERO }],
  ["delta < 1/8", { delta: q(1n, 8n) }],
  ["alpha exponent 1/4+epsilon/4 < 1/2", { epsilon: ONE }],
  ["gamma exponent 1/2+3*epsilon/2 < 1", { epsilon: q(1n, 3n) }],
  ["epsilon*c > 0", { c: ZERO }],
  ["epsilon*c < 1 - epsilon", { c: div(sub(ONE, PC.epsilon), PC.epsilon) }],
  ["1 - epsilon > 0", { epsilon: ONE }],
  ["kappa > 0", { kappa: ZERO }],
  [
    [
      "eps C1 = 99872039/10^8",
      "alpha exponent 1/4 + eps/4 = 11999/40000",
      "gamma exponent 1/2 + 3 eps/2 = 15997/20000",
      "prime-interval exponent 1 - 2 eps = 3001/5000",
      "K exponent eps c = 1999/50000",
      "ell exponent 1 - eps = 8001/10000",
      "G_* = 333833/(4*10^15)",
      "G_* - kappa = 1833/(4*10^15)",
      "kappa < g3",
    ],
    { epsilon: eps1988 },
  ],
  [["chi_reserve = 1 - c = 4/5", "G_* = g3", "kappa < g2"], { c: q(14n, 100n) }],
  ["kappa < g4", { tau: ONE }],
  ["kappa < g7", { kappa: PC.epsilon }],
  ["kappa > 2^-34", { kappa: twoPow(-34) }],
  ["kappa < 2^-33", { kappa: twoPow(-33) }],
  ["C1 = 5 - 4 beta + zeta (<=)", { C1: add(PC.C1, q(1n, 10000n)) }],
  ["C1 = 5 - 4 beta + zeta (>=)", { C1: q(2n) }],
  ["b >= 2^40 gives 46 b^e <= b/4 (e = 1/2 + 3 eps/2 = u/v): 184^v <= 2^(40(v-u))", { epsilon: q(1n, 3n) }],
  [[40, 41, 48, 64, 100].map((e) => `b = 2^${e}: alpha, gamma meet every stated bound`), { epsilon: q(1n, 3n) }],
  // 82.8/10^12 is below 99% of upper/5 (about 82.86/10^12)
  ["witness exceeds 99% of the upper enclosure: kappa > (99/100) upper/5", { kappa: q(828n, TEN(13)) }],
];
for (const [names, p] of pC) add_("compact", `parameters for ${Array.isArray(names) ? names[0] : names}`, names, () => runCompact({ p }));
add_("compact", "complex network at h = 6", "h_c = 25 > 6 (a coordinate outside six; 3^j < 25^j)", () => runCompact({ h: 6 }));
// L_c / N_c = 18(h+1)/((h-1)(h-2)) is at least 1 for h <= 21
add_("compact", "complex network at h = 21", "L_c < N_c (the positivity the note needs)", () => runCompact({ h: 21 }));
add_("compact", "complex network at h = 50", "2 L_c < N_c fails at h = 25 (the note says it is not needed)", () => runCompact({ h: 50 }));

// ------------------------------------------------------------------ rows the runner cannot be made to fail
/** Counted rows whose inputs the runner does not expose, with the test that makes the underlying function fail. */
const NOT_RUNNER_FAILABLE: Record<Group, Record<string, string>> = {
  bit: {
    "h = 50 is admissible: h > 6 (spare coordinates) and h != 9 (I - J/9 nondegenerate)": "constant; circuit.test.ts 'exceptional eigenvalue ... 0 at h = 9'",
  },
  "59": {
    "m >= 3": "each-check.test.ts '2^-59 guard: m = 2, s = 1, beta = 89/100'",
    "s >= 2": "each-check.test.ts '2^-59 guard: m = 2, s = 1, beta = 89/100'",
    "s < m^5": "downstream.test.ts 's >= m^5 would break s^j <= s d^(5(1-beta))'",
    "36 < 128 (36 m B^2 < C0 = 128 m B^2)": "constant of stopped-guard.tex; no failure mode",
    "unrolled depth recurrence obeys both stated bounds on all samples": "downstream.test.ts 'depth samples reject a recurrence that outgrows either bound'",
  },
  compact: {
    "m >= 3 (also gives log m > 1)": "each-check.test.ts 'compact guard: m = 2, s = 1, ...'",
    "s >= 2": "each-check.test.ts 'compact guard: m = 2, s = 1, ...'",
    "s < m^5": "compact.test.ts 's = m^5 fails s < m^5; ...'",
    "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta) (<= 9B^2 d^(5-4beta) follows)":
      "compact.test.ts 'failure mode: a branching factor s = m^6 ...'; each-check.test.ts 'the intermediate bound ...'",
    "184 < 2^8 = 2^(40/5)": "constant of compact-control-note.tex; no failure mode",
    "delta = n(2*2^-G + 8*2^(G-K)) <= 5/(128 p^3) at the cutoff K = G + 4 ceil(log2 p) + 10, n = p, p = 2..4096":
      "lemma sample; compact.test.ts 'one bit below the cutoff ... fails'",
    "2/64 + 8/1024 = 5/128 (the constant of the general step, all p >= 2)": "constant of compact-control-movement.tex; no failure mode",
    "four-update identity: final v = v + z(1-2a), dirty temporary restored (all v, w in [-40,40])": "lemma sample; compact.test.ts 'the four updates toggle ...'",
    "good digits (w <= B-2): load stays in its digit; target displacement at most 2B (G = 1..4)": "lemma sample; compact.test.ts 'a saturated digit B - 1 ... overflows'",
    "later source: control parities differ by exactly x; temporaries restored (G = 1..4)": "lemma sample; compact.test.ts 'a saturated digit B - 1 ... overflows'",
  },
};

// ------------------------------------------------------------------ tests
const published = (): Record<Group, Result[]> => ({ bit: runBit(), "59": run59(), compact: runCompact() });

describe("runners: the published witnesses pass every row", () => {
  test("no row fails in the bit network, the 2^-59 witness or the compact-control witness", () => {
    const p = published();
    expect([...failures(p.bit), ...failures(p["59"]), ...failures(p.compact)]).toEqual([]);
  }, 60_000);
});

describe("runners: each change makes the named rows fail", () => {
  for (const c of cases)
    test(`[${c.group}] ${c.label}`, () => {
      const f = failures(c.run());
      for (const name of c.expect) expect(f).toContain(name);
    }, 60_000);
});

describe("runners: every counted row has a failure test", () => {
  const p = published();
  for (const g of ["bit", "59", "compact"] as Group[]) {
    test(`[${g}] each counted row is made to fail by a case above, or is listed with its function-level test`, () => {
      const killed = new Set(cases.filter((c) => c.group === g).flatMap((c) => c.expect));
      const exempt = NOT_RUNNER_FAILABLE[g];
      const uncovered = p[g].filter(isCounted).map((r) => r.name).filter((n) => !killed.has(n) && !(n in exempt));
      expect(uncovered).toEqual([]);
    });
    test(`[${g}] every name the cases expect, and every exempt name, is a counted row of the published run`, () => {
      const counted = new Set(p[g].filter(isCounted).map((r) => r.name));
      const named = [...cases.filter((c) => c.group === g).flatMap((c) => c.expect), ...Object.keys(NOT_RUNNER_FAILABLE[g])];
      expect(named.filter((n) => !counted.has(n))).toEqual([]);
    });
  }
});

describe("main.ts: the exit code follows the verdict", () => {
  test("a nudged parameter in each witness makes `bun run check` exit 1 and name both failures", () => {
    const r = Bun.spawnSync(["bun", `${import.meta.dir}/../src/main.ts`, "--no-observation", "--set=59.kappa=1/288230376151711744", "--set=compact.epsilon=1988/10000"]);
    const out = r.stdout.toString();
    expect(r.exitCode).toBe(1);
    expect(out).toContain("VERDICT 2^-59 witness (preserved): FAIL");
    expect(out).toContain("VERDICT compact-control witness (current): FAIL");
    expect(out).toContain("FAILED: [2^-59 witness (preserved)] kappa < G = min g_j");
    expect(out).toContain("FAILED: [compact-control witness (current)] kappa < g3");
  }, 120_000);
});
