// The paired-block circuit, its cross-group merge, and the stage matching.
import { describe, expect, test } from "bun:test";
import { buildPairedCircuit, PUBLISHED_CONVENTIONS, ALTERNATIVE_CONVENTIONS, pairIndex, type Circuit } from "../src/circuit";
import { verifyLocalCircuit, supportsOf } from "../src/verifyCircuit";
import { mergeGroups, verifyGlobal, tripleIndex, tripleList, type GlobalGraph } from "../src/global";
import { checkMatching, piMatching, form, indicator, exceptionalEigenvalue } from "../src/matching";
import { q, eq, add, mul, lt, ZERO, type Q } from "../src/rational";
import { binom } from "../src/intmath";

const exactAndClean = (c: Circuit) => {
  const r = verifyLocalCircuit(c);
  return r.allOutputSupportsExact && r.allAdditionsDisjoint && r.everyAdditionUsed;
};

describe("local circuit: exact for every size", () => {
  test("outputs equal sum_{ {a,b} disjoint from {c,d} } x_ab for n = 4..40, both conventions", () => {
    for (let n = 4; n <= 40; n++)
      for (const conv of [PUBLISHED_CONVENTIONS, ALTERNATIVE_CONVENTIONS]) expect(exactAndClean(buildPairedCircuit(n, conv))).toBe(true);
  });
  test("nonzero coefficients = C(n,2) * C(n-2,2) (each output has C(n-2,2) terms)", () => {
    for (const n of [5, 12, 49]) {
      const r = verifyLocalCircuit(buildPairedCircuit(n));
      expect(BigInt(r.nonzeroCoefficients)).toBe(binom(n, 2) * binom(n - 2, 2));
    }
  });
  test("n = 49: 9813 additions with the published conventions, 9810 with the alternative", () => {
    expect(buildPairedCircuit(49, PUBLISHED_CONVENTIONS).left.length).toBe(9813);
    expect(buildPairedCircuit(49, ALTERNATIVE_CONVENTIONS).left.length).toBe(9810);
  });
});

describe("local circuit: the verifier rejects corrupted circuits", () => {
  const base = buildPairedCircuit(12);
  test("an output pointing at the wrong node is caught", () => {
    const outputs = base.outputs.slice();
    [outputs[0], outputs[1]] = [outputs[1]!, outputs[0]!];
    expect(verifyLocalCircuit({ ...base, outputs }).allOutputSupportsExact).toBe(false);
  });
  test("an addition with a changed operand is caught (overlap or wrong support)", () => {
    for (const k of [0, 17, base.left.length - 1]) {
      const left = base.left.slice();
      left[k] = left[k] === 0 ? 1 : 0; // replace an operand by an input
      const r = verifyLocalCircuit({ ...base, left });
      expect(r.allAdditionsDisjoint && r.allOutputSupportsExact).toBe(false);
    }
  });
  test("an output with one extra input term fails exactness (the required-zeros half)", () => {
    const n = base.n;
    const [c, d, e] = [0, 1, 2];
    const out = base.outputs[pairIndex(n, c, d)]!;
    const extra = pairIndex(n, c, e); // x_ce meets {c,d}, so it is not in supp(z_cd): the sum stays disjoint
    const left = [...base.left, out];
    const right = [...base.right, extra];
    const outputs = base.outputs.slice();
    outputs[pairIndex(n, c, d)] = base.inputs + base.left.length;
    const r = verifyLocalCircuit({ ...base, left, right, outputs });
    expect(r.allAdditionsDisjoint).toBe(true);
    expect(r.allOutputSupportsExact).toBe(false);
  });
  test("an output that adds one input twice has the right support as a set but fails disjointness (coefficient 2)", () => {
    // o = l + r is an output. Build t = r + x_k with x_k in supp(l), then o' = l + t:
    // supp(o') = supp(o) as sets, so only the disjointness flag sees the repeated x_k.
    const o = base.outputs[0]!;
    const [l, r] = [base.left[o - base.inputs]!, base.right[o - base.inputs]!];
    const sl = supportsOf(base)[l]!;
    let k = 0; // the first input in supp(l)
    while (((sl[k >>> 5]! >>> (k & 31)) & 1) === 0) k++;
    const t = base.inputs + base.left.length;
    const left = [...base.left, r, l];
    const right = [...base.right, k, t];
    const outputs = base.outputs.slice();
    outputs[0] = t + 1;
    const rep = verifyLocalCircuit({ ...base, left, right, outputs });
    expect(rep.allOutputSupportsExact).toBe(true);
    expect(rep.allAdditionsDisjoint).toBe(false);
  });
  test("an output missing terms (pointing at one of its own operands) fails exactness", () => {
    const k = base.outputs[0]! - base.inputs; // the addition computing output 0
    const outputs = base.outputs.slice();
    outputs[0] = base.left[k]!;
    expect(verifyLocalCircuit({ ...base, outputs }).allOutputSupportsExact).toBe(false);
  });
  test("an addition that no output uses is reported as unused", () => {
    const left = [...base.left, 0];
    const right = [...base.right, 1];
    const r = verifyLocalCircuit({ ...base, left, right });
    expect(r.everyAdditionUsed).toBe(false);
    expect(r.allOutputSupportsExact && r.allAdditionsDisjoint).toBe(true);
  });
  test("an operand that refers forward in time is rejected", () => {
    const left = base.left.slice();
    left[0] = base.inputs + base.left.length - 1;
    expect(() => verifyLocalCircuit({ ...base, left })).toThrow();
  });
});

/** Explicit support of every global node, as a sorted list of triple indices (small h only). */
function globalSupports(G: GlobalGraph): number[][] {
  const s: number[][] = [];
  for (let t = 0; t < G.inputs; t++) s.push([t]);
  for (let k = 0; k < G.left.length; k++) s.push([...s[G.left[k]!]!, ...s[G.right[k]!]!].sort((a, b) => a - b));
  return s;
}

describe("global merge across common-point groups", () => {
  test("h = 6..16: exact partial outputs, disjoint additions, common points, every node used", () => {
    for (let h = 6; h <= 16; h++) {
      const r = verifyGlobal(mergeGroups(buildPairedCircuit(h - 1), h));
      expect(r.allPartialOutputsExact && r.allAdditionsDisjoint && r.everyNodeHasCommonPoint && r.everyNodeUsed && r.outputsOrthogonalToTarget).toBe(true);
      expect(r.partialOutputs).toBe(h * Number(binom(h - 1, 2)));
    }
  });

  describe("the global verifier rejects corrupted graphs (h = 8)", () => {
    const h = 8;
    const n = h - 1;
    const G = mergeGroups(buildPairedCircuit(n), h);
    const total = G.inputs + G.left.length;
    const withAddition = (l: number, r: number) => ({ ...G, left: [...G.left, l], right: [...G.right, r], id: total });
    test("the uncorrupted graph passes every flag", () => {
      const r = verifyGlobal(G);
      expect([r.allPartialOutputsExact, r.outputsOrthogonalToTarget, r.everyNodeHasCommonPoint, r.allAdditionsDisjoint, r.everyNodeUsed]).toEqual([true, true, true, true, true]);
    });
    test("one output pointer swapped: exactness and orthogonality fail, common point holds", () => {
      const outputs = G.outputs.slice();
      const [x, y] = [pairIndex(n, 0, 1), pairIndex(n, 0, 2)]; // targets {i,0,1} and {i,0,2} in group i = 0
      [outputs[x], outputs[y]] = [outputs[y]!, outputs[x]!];
      const r = verifyGlobal({ ...G, outputs });
      expect(r.allPartialOutputsExact).toBe(false);
      expect(r.outputsOrthogonalToTarget).toBe(false); // z_{0,2} contains triples {i,1,b}, which meet {i,0,1} in two points
      expect(r.everyNodeHasCommonPoint).toBe(true);
    });
    test("an output missing terms fails exactness but stays orthogonal (the two flags are distinct)", () => {
      const outputs = G.outputs.slice();
      outputs[0] = G.left[outputs[0]! - G.inputs]!; // one operand of the output sum
      const r = verifyGlobal({ ...G, outputs });
      expect(r.allPartialOutputsExact).toBe(false);
      expect(r.outputsOrthogonalToTarget).toBe(true);
    });
    test("an output with one extra triple meeting the target in two points fails exactness and orthogonality", () => {
      // group i = 0, target T = {0, g(0), g(1)} = {0,1,2}; add the triple {0,1,3}, which meets T in {0,1}
      const k = pairIndex(n, 0, 1);
      const G2 = withAddition(G.outputs[k]!, tripleIndex(h, [0, 1, 3]));
      const outputs = G.outputs.slice();
      outputs[k] = G2.id;
      const r = verifyGlobal({ ...G2, outputs });
      expect(r.allAdditionsDisjoint).toBe(true);
      expect(r.allPartialOutputsExact).toBe(false);
      expect(r.outputsOrthogonalToTarget).toBe(false);
    });
    test("a node whose triples have no common point fails the common-point flag", () => {
      // {0,1,2} + {3,4,5}: no point lies in both; route group 0's first output through it
      const G2 = withAddition(tripleIndex(h, [0, 1, 2]), tripleIndex(h, [3, 4, 5]));
      const outputs = G.outputs.slice();
      outputs[0] = G2.id;
      const r = verifyGlobal({ ...G2, outputs });
      expect(r.everyNodeHasCommonPoint).toBe(false);
      expect(r.allPartialOutputsExact).toBe(false);
    });
    test("an addition of overlapping supports fails the disjointness flag", () => {
      const t = tripleIndex(h, [0, 1, 2]);
      const G2 = withAddition(t, t);
      const outputs = G.outputs.slice();
      outputs[0] = G2.id;
      expect(verifyGlobal({ ...G2, outputs }).allAdditionsDisjoint).toBe(false);
    });
    test("an addition that nothing uses fails the every-node-used flag", () => {
      const r = verifyGlobal(withAddition(tripleIndex(h, [0, 1, 2]), tripleIndex(h, [0, 3, 4])));
      expect(r.everyNodeUsed).toBe(false);
      expect(r.allPartialOutputsExact).toBe(true);
    });
  });

  test("brute force, h = 7..14: merging identifies exactly the equal supports (explicit triple sets)", () => {
    for (let h = 7; h <= 14; h++) {
      const local = buildPairedCircuit(h - 1);
      const G = mergeGroups(local, h);
      const sup = globalSupports(G);
      // no two global additions with the same support remain
      const keys = sup.slice(G.inputs).map((x) => x.join(","));
      expect(new Set(keys).size).toBe(keys.length);
      // recount the distinct supports among all groups' local additions directly
      const ls = supportsOf(local);
      const pairs: [number, number][] = [];
      for (let a = 0; a < h - 1; a++) for (let b = a + 1; b < h - 1; b++) pairs[pairIndex(h - 1, a, b)] = [a, b];
      const distinct = new Set<string>();
      for (let i = 0; i < h; i++) {
        const g = (u: number) => (u < i ? u : u + 1);
        for (let id = local.inputs; id < ls.length; id++) {
          const triples: number[] = [];
          for (let k = 0; k < local.inputs; k++)
            if ((ls[id]![k >>> 5]! >>> (k & 31)) & 1) triples.push(tripleIndex(h, [i, g(pairs[k]![0]), g(pairs[k]![1])]));
          distinct.add(triples.sort((a, b) => a - b).join(","));
        }
      }
      expect(G.left.length).toBe(distinct.size);
      expect(G.mergedAdditions).toBe(h * local.left.length - distinct.size);
    }
  });

  test("h = 7..12: the injected outputs give exactly the intersection-one matrix", () => {
    // For a target T, the three groups i in T each inject z_{T \ {i}}; together they must
    // be a disjoint cover of { S : |S cap T| = 1 } ("every neighbor pair has a unique common point").
    for (let h = 7; h <= 12; h++) {
      const G = mergeGroups(buildPairedCircuit(h - 1), h);
      const sup = globalSupports(G);
      const triples = tripleList(h);
      const n = h - 1;
      const P = (n * (n - 1)) / 2;
      for (const T of triples) {
        const got: number[] = [];
        for (const i of T) {
          const [c, d] = T.filter((x) => x !== i).map((x) => (x < i ? x : x - 1)) as [number, number]; // local labels
          got.push(...sup[G.outputs[i * P + pairIndex(n, c, d)]!]!);
        }
        const want = triples.map((S, idx) => [S, idx] as const).filter(([S]) => S.filter((x) => T.includes(x)).length === 1).map(([, idx]) => idx);
        expect(got.sort((a, b) => a - b)).toEqual(want); // equal as multisets => disjoint cover
      }
    }
  });

  test("h = 50: c = 450394, merged = 40256, R = c + q = 509194 (published conventions)", () => {
    const r = verifyGlobal(mergeGroups(buildPairedCircuit(49, PUBLISHED_CONVENTIONS), 50));
    expect([r.additions, r.mergedAdditions, r.partialOutputs, r.roles]).toEqual([450394, 40256, 58800, 509194]);
    expect(r.allPartialOutputsExact && r.everyNodeHasCommonPoint && r.allAdditionsDisjoint && r.everyNodeUsed).toBe(true);
  }, 120_000);
});

describe("the rational form I - J/9 and the stage matching pi", () => {
  test("triple vectors have norm 2; intersection-one triples are orthogonal", () => {
    const h = 50;
    expect(eq(form(indicator(h, [0, 1, 2]), indicator(h, [0, 1, 2])), q(2n))).toBe(true);
    expect(eq(form(indicator(h, [0, 1, 2]), indicator(h, [0, 3, 4])), ZERO)).toBe(true);
    expect(eq(form(indicator(h, [0, 1, 2]), indicator(h, [0, 1, 4])), q(1n))).toBe(true);
  });
  test("exceptional eigenvalue 1 - h/9: -41/9 at h = 50, and 0 at h = 9 (the excluded case)", () => {
    expect(eq(exceptionalEigenvalue(50), q(-41n, 9n))).toBe(true);
    expect(eq(exceptionalEigenvalue(9), ZERO)).toBe(true);
    const ones = new Array(9).fill(q(1n));
    expect(eq(form(ones, indicator(9, [0, 1, 2])), ZERO)).toBe(true); // all-ones is in the radical at h = 9
  });
  test("common point => sum u_j = 3 u_i and <u,u> = sum_{j != i} u_j^2 > 0 (random spans, h = 50)", () => {
    let x = 12345;
    const r = () => ((x = (Math.imul(x, 1103515245) + 12345) >>> 0) % 7) - 3;
    const h = 50;
    const triples = tripleList(h);
    for (let trial = 0; trial < 60; trial++) {
      const i = trial % h;
      const containing = triples.filter((T) => T.includes(i));
      let u: Q[] = new Array(h).fill(ZERO);
      for (let k = 0; k < 6; k++) {
        const T = containing[(trial * 97 + k * 389) % containing.length]!;
        const coef = q(BigInt(r()), BigInt(1 + ((trial + k) % 4)));
        u = u.map((uj, j) => (T.includes(j) ? add(uj, coef) : uj));
      }
      const total = u.reduce(add, ZERO);
      expect(eq(total, mul(q(3n), u[i]!))).toBe(true);
      const rest = u.reduce((s, uj, j) => (j === i ? s : add(s, mul(uj, uj))), ZERO);
      expect(eq(form(u, u), rest)).toBe(true);
      if (!u.every((uj) => eq(uj, ZERO))) expect(lt(ZERO, form(u, u))).toBe(true);
    }
  });
  test("pi is a bijection with |T cap pi(T)| = 1 for even h = 6..20 and h = 50", () => {
    for (const h of [6, 8, 10, 12, 14, 16, 18, 20, 50]) {
      const m = checkMatching(h);
      expect(m.bijective && m.intersectionOne && m.joiningLabelsNested).toBe(true);
    }
  });
  test("failure mode: cycling the full pair among ALL pairs (not skipping the singleton's) is rejected", () => {
    const h = 10;
    const wrong = (T: number[]) => {
      const [x, y, z] = T as [number, number, number];
      for (const [p1, p2, s] of [[x, y, z], [x, z, y], [y, z, x]] as const)
        if (p1 >> 1 === p2 >> 1) {
          const next = ((p1 >> 1) + 1) % (h / 2);
          return [s, 2 * next, 2 * next + 1].sort((a, b) => a - b);
        }
      return piMatching(h, T);
    };
    // landing on the singleton's own pair produces {s, s, partner(s)}: not a triple, so not a bijection of triples
    expect(checkMatching(h, wrong).bijective).toBe(false);
  });
  test("failure mode: a non-injective map with |A cap pi(A)| = 1 everywhere fails only bijectivity", () => {
    const h = 10;
    const triples = tripleList(h);
    const A1 = triples[0]!;
    const target = piMatching(h, A1);
    const A0 = triples.find((T) => T.join() !== A1.join() && T.filter((x) => target.includes(x)).length === 1)!;
    const wrong = (T: number[]) => (T.join() === A0.join() ? target : piMatching(h, T)); // A0 and A1 share an image
    const m = checkMatching(h, wrong);
    expect(m.bijective).toBe(false);
    expect(m.intersectionOne && m.joiningLabelsNested).toBe(true);
  });
  test("failure mode: the identity map is a bijection but |A cap A| = 3 and <t_A, t_A> = 2", () => {
    const m = checkMatching(10, (T) => T);
    expect(m.bijective).toBe(true);
    expect(m.intersectionOne).toBe(false);
    expect(m.joiningLabelsNested).toBe(false);
  });
});
