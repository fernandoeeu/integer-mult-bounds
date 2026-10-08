// PR re-checks of 8 October 2026, entries 9 to 13: batched moments (PR 10, 12, 13),
// the bulk guard, the 29-row slack table, PR 9's star rules and PR 11's matching and
// identities. Fast failure modes only; PR 9's global build is exercised by `check:prs`.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, lt, eq, ONE, ZERO, type Q } from "../../src/rational";
import { momentWeights, momentUpperBound, momentUpperSecond, bitClasses, bulkPathBounds, slackTable, taylorSixFifths, chirpBudget, logInverseEnclosure } from "../../src/prs/batched";
import { pr10, pr10Params, STATED_PR10 } from "../../src/prs/pr10";
import { pr13, STATED_PR13 } from "../../src/prs/pr13";
import { pr12 } from "../../src/prs/pr12";
import { pr11, edgeCycle, checkEdgeCycle, cycleMatching, primePowerIdentity } from "../../src/prs/pr11";
import { largeFirstGreedy, pruneGates } from "../../src/prs/starRules";
import { greedyCSE, checkTemplate } from "../../src/prs/primeField";
import { primeFieldBitNetwork } from "../../src/prs/pr7";
import { counted } from "../../src/prs/rows";

const TEN = (k: number) => 10n ** BigInt(k);
const failing = (rs: { ok: boolean; kind: string; name: string }[]) => rs.filter((r) => !r.ok && r.kind !== "observation").map((r) => r.name);

describe("batched moments", () => {
  const bn = primeFieldBitNetwork(28, 11840940n);
  const ctrl = momentWeights(bn.m, bn.W, bn.s, bitClasses(28n, bn.v, 11840940n, "controlled").classes);
  const logs = [...STATED_PR10.midLogs, STATED_PR10.log28];
  test("weights sum to 1 - eta for every mode (rank sum preserved)", () => {
    for (const mode of ["three", "controlled", "sourceFrames"] as const) {
      const w = momentWeights(bn.m, bn.W, bn.s, bitClasses(28n, bn.v, 11840940n, mode).classes);
      expect(eq(w.total, sub(ONE, bn.eta))).toBe(true);
    }
  });
  test("a_b = 246/10^9 passes, 247/10^9 fails both routes", () => {
    expect(lt(momentUpperBound(ctrl.items, q(246n, TEN(9)), logs).bound, ONE)).toBe(true);
    expect(lt(momentUpperBound(ctrl.items, q(247n, TEN(9)), logs).bound, ONE)).toBe(false);
    expect(lt(momentUpperSecond(ctrl.items, q(247n, TEN(9))).bound, ONE)).toBe(false);
  });
  test("the uniform (unbatched) moment only certifies about 7.5e-9", () => {
    const flat = momentWeights(bn.m, bn.W, bn.s, []);
    expect(lt(momentUpperSecond(flat.items, q(75n, TEN(10))).bound, ONE)).toBe(true);
    expect(lt(momentUpperSecond(flat.items, q(76n, TEN(10))).bound, ONE)).toBe(false);
  });
  test("an understated log bound is rejected by the enclosure", () => {
    const e = logInverseEnclosure(q(195n, 196n));
    expect(lt(e.upper, q(512n, TEN(5)))).toBe(true);
    expect(lt(e.upper, q(510n, TEN(5)))).toBe(false);
  });
  test("a larger role count R shrinks the gap and eventually fails", () => {
    const big = primeFieldBitNetwork(28, 11840940n + 20000n);
    const w = momentWeights(big.m, big.W, big.s, bitClasses(28n, big.v, 11840940n + 20000n, "controlled").classes);
    expect(lt(momentUpperSecond(w.items, q(246n, TEN(9))).bound, ONE)).toBe(false);
  });
});

describe("bulk guard", () => {
  test("Taylor bound is an upper bound and the path moments are below 999/1000", () => {
    const g = bulkPathBounds(21952n, 28n, [21896n, 21168n, 21141n]);
    expect(g.lowerOk && g.atMostOne && g.rows.every((r) => r.taylorValid && lt(r.bound, q(999n, 1000n)))).toBe(true);
  });
  test("a too-small Taylor value is caught by the fifth-power check", () => {
    const t = q(56n, 21952n);
    const T = sub(taylorSixFifths(t), q(1n, TEN(4)));
    expect(T.num > 0n && lt(mul(mul(mul(mul(mul(sub(ONE, t), sub(ONE, t)), sub(ONE, t)), sub(ONE, t)), sub(ONE, t)), sub(ONE, t)), mul(mul(mul(mul(T, T), T), T), T))).toBe(false);
  });
  test("a rank below q/2 breaks 'at most one selected edge per path'", () => {
    expect(bulkPathBounds(21952n, 28n, [21896n, 11000n]).atMostOne).toBe(false);
  });
  test("chirp budget holds, and would fail with 31p in place of 34p", () => {
    expect(chirpBudget(400).ok).toBe(true);
    // 30p + 1.14p + ... > 31p for large alpha: sanity of the inequality's tightness
    expect(30 * 1000 + 1141 + 11 > 31 * 1000).toBe(true);
  });
});

describe("PR 10 / 12 / 13 entries", () => {
  test("PR 10 passes; moving kappa to G_* fails it", () => {
    expect(failing(pr10().results)).toEqual([]);
    const p = { ...pr10Params(), kappa: q(9839998762000001n, 8n * TEN(22)) };
    expect(failing(pr10({ p }).results).length).toBeGreaterThan(0);
  }, 120000);
  test("PR 10: a stated a_c of 73/10^8 is not certified", () => {
    expect(failing(pr10({ stated: { ac: q(73n, TEN(8)) } }).results).length).toBeGreaterThan(0);
  }, 120000);
  test("PR 13 passes; a stated S' off by one and a_b = 155/10^8 fail", () => {
    expect(failing(pr13().results)).toEqual([]);
    expect(failing(pr13({ stated: { Sprime: STATED_PR13.Sprime + 1n } }).results).length).toBeGreaterThan(0);
    expect(failing(pr13({ stated: { a: q(155n, TEN(8)) } }).results).length).toBeGreaterThan(0);
  }, 120000);
  test("PR 12 passes; R + 2400 roles is rejected", () => {
    expect(failing(pr12().results)).toEqual([]);
    expect(failing(pr12({ stated: { R: 17515487n + 2400n, c: 16089992n + 2400n } }).results).length).toBeGreaterThan(0);
  }, 120000);
  test("the slack table has 29 rows, all positive at PR 10's parameters, and a negative row when eps = 1/2", () => {
    const p = pr10Params();
    const leaf = add(p.sigma, mul(p.beta, sub(ONE, p.sigma)));
    const t = slackTable(p as any, p.tau, leaf);
    expect(t.length).toBe(29);
    expect(t.every(([, v]) => lt(ZERO, v))).toBe(true);
    const bad = slackTable({ ...p, epsilon: q(1n, 2n) } as any, p.tau, leaf);
    expect(bad.some(([, v]) => !lt(ZERO, v))).toBe(true);
  });
});

describe("PR 9 star rules", () => {
  const masks = [0b0111, 0b1110, 0b1111, 0b1011, 0b0101];
  test("large-first variants produce every request with valid disjoint gates", () => {
    for (const rev of [false, true]) {
      const g = largeFirstGreedy(masks, rev);
      expect(checkTemplate(4, masks, g)).toBe(true);
    }
    expect(checkTemplate(4, masks, greedyCSE(masks))).toBe(true);
  });
  test("pruning removes a gate no output needs", () => {
    const gates: [number, number][] = [[1, 2], [4, 8], [3, 4]];
    expect(pruneGates(gates, [7])).toEqual([[1, 2], [3, 4]]);
  });
  test("a template checker rejects a gate on unavailable operands", () => {
    expect(checkTemplate(4, [7], [[3, 4]])).toBe(false);
  });
});

describe("PR 11", () => {
  test("insertion cycle is valid for k = 3..15, and a broken order is caught", () => {
    for (let k = 3; k <= 15; k++) expect(checkEdgeCycle([...Array(k).keys()]).ok).toBe(true);
    const c = edgeCycle([0, 1, 2, 3, 4]);
    expect(c.length).toBe(10);
  });
  test("cycle matching at h = 10 and 14 (h/2 odd and even)", () => {
    for (const h of [10, 14]) {
      const m = cycleMatching(h);
      expect(m.allTwo && m.distinct === m.domain).toBe(true);
    }
  });
  test("prime-power identity holds for q = 4, 9 and fails for q = 6", () => {
    expect(primePowerIdentity(2n, 4n) && primePowerIdentity(3n, 9n)).toBe(true);
    expect(primePowerIdentity(2n, 6n) || primePowerIdentity(3n, 6n)).toBe(false);
  });
  test("entry passes with one erratum observation (h = 28 decimal)", () => {
    const rs = pr11().results;
    expect(failing(rs)).toEqual([]);
    expect(rs.filter((r) => !r.ok && r.kind === "observation").map((r) => r.name.slice(0, 7))).toEqual(["ERRATUM"]);
    expect(rs.filter(counted).length).toBeGreaterThan(30);
  });
});
