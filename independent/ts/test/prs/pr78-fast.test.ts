// PR re-checks of 8 October 2026, later entries: PR 7 (F3 five-subset bit network,
// paired complex producer) and PR 8 (geometric complex-network candidate). The fast
// part: small instances rebuilt and verified a second way by brute force, function-level
// failure modes, and corrupted inputs that the verifiers must reject.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, lt, le, eq, ONE, type Q } from "../../src/rational";
import { holds } from "../../src/parameters";
import { compactParameterChecks, compactMinimumMargin } from "../../src/compact/witness";
import { fastParameterChecks, fastMinimumMargin, fastMargins } from "../../src/prs/fastGaussian";
import { buildPairedTriple, verifyPairedTriple, type ActiveGraph } from "../../src/prs/pairedTriple";
import { mergeProducers, prune, starDemands, resynthesize, fingerprintCount, greedyCSE, checkTemplate, canonicalRequests, contextOrder } from "../../src/prs/primeField";
import { buildComplexCircuit, verifyComplexCircuit } from "../../src/prs/complexCircuit";
import { pr7Params, primeFieldBitNetwork, primeFieldComplexNetwork, fiveSetMatching, retainedSpanRank, largestR } from "../../src/prs/pr7";
import { pr8Params, geometricNetwork, bitScreenCase } from "../../src/prs/pr8";
import { dyadicCircuit, disjointRequests, intersectionTwoRequests, sideMapExact, sideMapExactFor, triplesLex } from "../../src/prs/geometric";

const TEN = (k: number) => 10n ** BigInt(k);
const pop = (x: number) => {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
};

describe("PR 7: the triple-exclusion producer", () => {
  test("n = 10, 18: every output exact, every addition disjoint, retained total exact", () => {
    for (const n of [10, 18]) {
      const r = buildPairedTriple(n, true).report;
      expect([n, r.outputsExact, r.allDisjoint, r.totalExact]).toEqual([n, true, true, true]);
    }
  });
  const g = buildPairedTriple(10, true).graph;
  test("an output pointer moved to another output is rejected", () => {
    const bad: ActiveGraph = { ...g, outputs: Int32Array.from(g.outputs) };
    bad.outputs[0] = g.outputs[1]!;
    expect(verifyPairedTriple(bad).outputsExact).toBe(false);
  });
  test("an addition that sums an input twice is rejected (overlap), and its output is no longer exact", () => {
    const bad: ActiveGraph = { ...g, left: Int32Array.from(g.left), right: Int32Array.from(g.right) };
    // first addition whose two children are inputs: make it x + x
    const k = [...bad.left].findIndex((a, i) => a <= g.V && bad.right[i]! <= g.V);
    bad.right[k] = bad.left[k]!;
    const r = verifyPairedTriple(bad);
    expect(r.allDisjoint).toBe(false);
  });
  test("the retained total pointer moved to an output is rejected", () => {
    expect(verifyPairedTriple({ ...g, total: g.outputs[0]! }).totalExact).toBe(false);
  });
  test("a total missing only the first input is rejected", () => {
    // append a chain x_2 + x_3 + ... + x_V and point the total at it
    const L = [...g.left];
    const R = [...g.right];
    let acc = 2;
    for (let i = 3; i <= g.V; i++) {
      L.push(acc);
      R.push(i);
      acc = g.V + L.length;
    }
    expect(verifyPairedTriple({ ...g, left: Int32Array.from(L), right: Int32Array.from(R), total: acc }).totalExact).toBe(false);
  });
});

/** Brute force at small h: explicit five-set supports of every global node, from the merged decompositions only. */
function bruteGlobal(h: number) {
  const local = buildPairedTriple(h - 2, true);
  const G = mergeProducers(h, local.graph);
  const fives: number[] = [];
  for (let m = 0; m < 1 << h; m++) if (pop(m) === 5) fives.push(m);
  const idx = new Map<number, number>();
  fives.forEach((m, i) => idx.set(m, i));
  const words = (fives.length + 31) >>> 5;
  const N = G.left.length;
  const sup: Uint32Array[] = new Array(N);
  let disjoint = true;
  for (let x = 1; x < N; x++) {
    const s = new Uint32Array(words);
    if (x <= G.v) {
      const i = idx.get(G.core[x]!)!;
      s[i >>> 5]! |= 1 << (i & 31);
    } else {
      const a = sup[G.left[x]!]!;
      const b = sup[G.right[x]!]!;
      for (let w = 0; w < words; w++) {
        if ((a[w]! & b[w]!) !== 0) disjoint = false;
        s[w] = a[w]! | b[w]!;
      }
    }
    sup[x] = s;
  }
  const has = (s: Uint32Array, i: number) => ((s[i >>> 5]! >>> (i & 31)) & 1) === 1;
  // roots: per context C (lexicographic), C(h-2,3) outputs in local triple order, then the total
  let exact = true;
  let r = 0;
  const n = h - 2;
  for (let ca = 0; ca < h; ca++)
    for (let cb = ca + 1; cb < h; cb++) {
      const C = (1 << ca) | (1 << cb);
      const order = contextOrder(h, ca, cb);
      for (let a = 0; a < n; a++)
        for (let b = a + 1; b < n; b++)
          for (let c = b + 1; c < n; c++) {
            const E = (1 << order[a]!) | (1 << order[b]!) | (1 << order[c]!);
            const s = sup[G.roots[r++]!]!;
            fives.forEach((T, i) => {
              if (has(s, i) !== ((T & C) === C && (T & E) === 0)) exact = false;
            });
          }
      const s = sup[G.roots[r++]!]!;
      fives.forEach((T, i) => {
        if (has(s, i) !== ((T & C) === C)) exact = false;
      });
    }
  const keys = new Set<string>();
  for (let x = G.v + 1; x < N; x++) keys.add(Array.from(sup[x]!).join(","));
  // stars: the common points of a node's support, recomputed from the support
  let coreOk = true;
  for (let x = G.v + 1; x < N; x++) {
    let c = (1 << h) - 1;
    fives.forEach((T, i) => {
      if (has(sup[x]!, i)) c &= T;
    });
    if (c !== G.core[x]) coreOk = false;
  }
  return { G, local, disjoint, exact, distinctSupports: keys.size, coreOk };
}

describe("PR 7: the global producer, rebuilt at small h and checked by brute force", () => {
  for (const h of [8, 10, 12]) {
    test(`h = ${h}: every root is exactly D_{C,E} or A_C, every addition disjoint, one node per support, cores right`, () => {
      const b = bruteGlobal(h);
      expect(b.disjoint).toBe(true);
      expect(b.exact).toBe(true);
      expect(b.coreOk).toBe(true);
      expect(b.distinctSupports).toBe(b.G.uniqueAdditions);
      expect(fingerprintCount(h, b.local.graph).distinct).toBe(b.G.uniqueAdditions);
      expect(b.G.roots.length).toBe(Number((BigInt(h) * BigInt(h - 1)) / 2n) * (1 + ((h - 2) * (h - 3) * (h - 4)) / 6));
    });
  }
  test("h = 12: stars, templates and the resynthesized count (a known value of this construction)", () => {
    const local = buildPairedTriple(10, true);
    const G = mergeProducers(12, local.graph);
    const pr = prune(G);
    const d = starDemands(G, pr.active);
    const rs = resynthesize(G, d);
    expect([pr.removed, d.stars, d.oldStarAdditions, rs.templates, rs.newStarAdditions, rs.allTemplatesValid]).toEqual([0, 495, 9660, 21, 9324, true]);
  });
});

describe("PR 7: the greedy rule and the template check", () => {
  test("greedy: the most frequent pair first; ties by union size, then union mask, then operands", () => {
    // {0,1} occurs in three requests, {2,3} in two
    const g = greedyCSE([0b0011, 0b0111, 0b1111, 0b1100]);
    expect(g[0]).toEqual([1, 2]);
    expect(checkTemplate(4, [0b0011, 0b0111, 0b1111, 0b1100], g)).toBe(true);
    // a tie between {0,1} and {2,3} (one occurrence each) goes to the smaller union mask
    expect(greedyCSE([0b0011, 0b1100])[0]).toEqual([1, 2]);
  });
  test("an already built union is reused (no second gate for the same sum)", () => {
    const g = greedyCSE([0b0011, 0b0011 | 0b0100, 0b0011]);
    const unions = g.map(([a, b]) => a | b);
    expect(new Set(unions).size).toBe(unions.length);
  });
  test("the template check rejects overlapping operands, unavailable operands, repeated sums and missing targets", () => {
    expect(checkTemplate(4, [0b0111], [[1, 2], [3, 1]])).toBe(false); // 3 and 1 are both available but overlap
    expect(checkTemplate(4, [0b0111], [[3, 4]])).toBe(false); // 3 is not available yet
    expect(checkTemplate(4, [0b0011], [[1, 2], [1, 2]])).toBe(false); // the same sum twice
    expect(checkTemplate(4, [0b0111], [[1, 2]])).toBe(false); // target not made
    expect(checkTemplate(4, [0b0111], [[1, 2], [3, 4]])).toBe(true);
  });
  test("context order: intact pairs in order, then the partners of the common pair's points", () => {
    expect(contextOrder(8, 0, 3)).toEqual([4, 5, 6, 7, 1, 2]);
    expect(contextOrder(8, 2, 3)).toEqual([0, 1, 4, 5, 6, 7]);
  });
  test("role budget: the largest R strictly below an integer bound", () => {
    // eta = 10 / (1 (0 + R)) > 1 * 1  <=>  R < 10
    expect(largestR(10n, 1n, 0n, q(1n), q(1n))).toBe(9n);
    expect(largestR(21n, 2n, 0n, q(1n), q(1n))).toBe(10n);
  });
  test("canonical relabelling: intact pairs first, then the partners of B's points", () => {
    // h = 8, B = {0, 2, 3, 4}: intact pair {6,7}; partners of 0 and 4: 1 and 5
    expect(canonicalRequests(8, 0b00011101, [1 << 6, 1 << 1, 1 << 5])).toEqual([1, 4, 8]);
  });
});

describe("PR 7: the bit network arithmetic", () => {
  test("eta_b(R) = (v - 6 C(h,2)(h-2)) / (2m (v + R)), and the role budget is sharp", () => {
    const a = q(3n, 400000000n);
    const L0 = q(9997n, 1000n);
    const v = 98280n;
    const Rmax = largestR(v - 6n * 378n * 26n, 2n * 21952n, v, a, L0);
    expect(lt(mul(a, L0), primeFieldBitNetwork(28, Rmax).eta)).toBe(true);
    expect(lt(mul(a, L0), primeFieldBitNetwork(28, Rmax + 1n).eta)).toBe(false);
    expect(Rmax).toBe(11844078n);
  });
  test("the complex role budget is sharp too", () => {
    const ac = q(39n, TEN(9));
    const R = largestR(3276n - 3n * 28n * 29n, 21952n, 3276n + 29n, ac, q(10n));
    expect(lt(mul(ac, q(10n)), primeFieldComplexNetwork(28, R).eta)).toBe(true);
    expect(lt(mul(ac, q(10n)), primeFieldComplexNetwork(28, R + 1n).eta)).toBe(false);
  });
  test("five-set matching at h = 8, 12: a bijection with |T cap pi(T)| = 2 (h = 10 has no Euler circuit)", () => {
    expect(() => fiveSetMatching(10)).toThrow();
    for (const h of [8, 12]) {
      const m = fiveSetMatching(h);
      expect([m.distinct, m.allTwo, m.classesPreserved]).toEqual([m.domain, true, true]);
    }
  });
  test("retained span: rank h - 2 at h = 8 and 12", () => {
    for (const h of [8, 12]) {
      const s = retainedSpanRank(h);
      expect([s.rankModP, s.relations]).toEqual([h - 2, true]);
    }
  });
});

describe("PR 7: the complex circuit with the paired producer (h = 12)", () => {
  test("side map exact and every addition disjoint", () => {
    const r = verifyComplexCircuit(buildComplexCircuit(12, "leftFold", false, buildPairedTriple(12, false).graph));
    expect([r.sideMapExact, r.allAdditionsDisjoint]).toEqual([true, true]);
  });
  test("a producer whose outputs are permuted makes the side map inexact", () => {
    const g = buildPairedTriple(12, false).graph;
    const outs = Int32Array.from(g.outputs);
    [outs[0], outs[1]] = [outs[1]!, outs[0]!];
    const r = verifyComplexCircuit(buildComplexCircuit(12, "leftFold", false, { ...g, outputs: outs }));
    expect(r.sideMapExact).toBe(false);
  });
});

const failing7 = (p: ReturnType<typeof pr7Params>) => fastParameterChecks(p).filter((k) => !holds(k)).map((k) => k.name);
describe("PR 7: parameters past their limits", () => {
  const P = pr7Params();
  test("the published parameters satisfy every condition; kappa < G_* = g3", () => {
    expect(failing7(P)).toEqual([]);
    expect(lt(P.kappa, fastMinimumMargin(P))).toBe(true);
    expect(eq(fastMinimumMargin(P), fastMargins(P).g3)).toBe(true);
  });
  const nudge = (label: string, p: typeof P, names: string[]) => test(label, () => {
    const f = failing7(p);
    for (const n of names) expect(f).toContain(n);
  });
  nudge("lambda = tau", { ...P, lambda: P.tau }, ["tau < lambda", "chi < lambda"]);
  nudge("lambda' at the leaf value", { ...P, lambdaPrime: sub(ONE, mul(sub(ONE, P.beta), sub(ONE, P.sigma))) }, ["sigma + beta(1-sigma) < lambda'"]);
  nudge("2 eps + delta = 1", { ...P, epsilon: div(sub(ONE, P.delta), q(2n)) }, ["2*epsilon + delta < 1"]);
  nudge("C1 = 1/eps", { ...P, C1: div(ONE, P.epsilon) }, ["epsilon*C1 < 1"]);
  test("kappa = G_* fails kappa < g3", () => {
    const p2 = { ...P, kappa: fastMinimumMargin(P) };
    expect(lt(p2.kappa, fastMargins(p2).g3)).toBe(false);
  });
});

describe("PR 8: the dyadic circuits", () => {
  test("n = 6, 7, 9: outputs exact, additions disjoint, side map exact", () => {
    for (const n of [6, 7, 9]) {
      const v = triplesLex(n).length;
      const D = dyadicCircuit(v, disjointRequests(n));
      const E = dyadicCircuit(v, intersectionTwoRequests(n).requests);
      expect([n, D.outputsExact, D.allDisjoint, E.outputsExact, E.allDisjoint, sideMapExact(n).exact]).toEqual([n, true, true, true, true, true]);
    }
  });
  test("the count does not depend on the order of the requests", () => {
    const req = disjointRequests(9);
    const a = dyadicCircuit(84, req).additions;
    const b = dyadicCircuit(84, [...req].reverse()).additions;
    expect(a).toBe(b);
  });
  test("the side-map comparison rejects E with the target left in, E or D with one triple missing", () => {
    const E = intersectionTwoRequests(7);
    const D = disjointRequests(7);
    expect(sideMapExactFor(7, D, E.requests, E.targets).exact).toBe(true);
    const badE = E.requests.map((r, k) => [...r, E.targets[k]!]);
    expect(sideMapExactFor(7, D, badE, E.targets).exact).toBe(false);
    const shortE = E.requests.map((r, k) => (k === 5 ? r.slice(1) : r));
    expect(sideMapExactFor(7, D, shortE, E.targets).exact).toBe(false);
    const badD = D.map((r, s) => (s === 3 ? r.slice(1) : r));
    expect(sideMapExactFor(7, badD, E.requests, E.targets).exact).toBe(false);
  });
});

describe("PR 8: network formulas and parameters", () => {
  test("eta = 68/1714426753 at R = 258557; one more role per invocation changes it", () => {
    expect(eq(geometricNetwork(25, 258557n).eta, q(68n, 1714426753n))).toBe(true);
    expect(eq(geometricNetwork(25, 258558n).eta, q(68n, 1714426753n))).toBe(false);
  });
  test("bit screen formulas at (50, 50) give the paired network's W and eta", () => {
    const r = bitScreenCase(50, 50, 509194n, 509194n);
    expect(r.W).toBe(406321422080000n);
    expect(eq(r.eta!, q(23n, 661055000n))).toBe(true);
  });
  const P = pr8Params();
  const failing8 = (p: typeof P) => compactParameterChecks(p).filter((k) => !holds(k)).map((k) => k.name);
  test("the published parameters satisfy every condition; G_* = g3", () => {
    expect(failing8(P)).toEqual([]);
    expect(lt(P.kappa, compactMinimumMargin(P))).toBe(true);
  });
  const nudge = (label: string, p: typeof P, names: string[]) => test(label, () => {
    const f = failing8(p);
    for (const n of names) expect(f).toContain(n);
  });
  nudge("c = 0", { ...P, c: q(0n) }, ["c > 0", "epsilon*c > 0"]);
  nudge("c with eps(1 + c) = 1", { ...P, c: sub(div(ONE, P.epsilon), ONE) }, ["epsilon(1+c) < 1"]);
  nudge("lambda' at the leaf value 1 - 3996/10^12", { ...P, lambdaPrime: sub(ONE, q(3996n, TEN(12))) }, ["sigma + beta(1-sigma) < lambda'"]);
  nudge("lambda = tau", { ...P, lambda: P.tau }, ["tau < lambda"]);
  nudge("eps = 1/5 (g5 and 3/4 + delta + 5eps/4 < 1)", { ...P, epsilon: q(1n, 5n) }, ["3/4 + delta + 5*epsilon/4 < 1"]);
});
