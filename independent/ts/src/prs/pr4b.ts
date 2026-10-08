// PR 4 (David Leen), new head 8c225e6: "Combine PR 3 shared exclusions with
// retained totals and stage sharing". Sources at prs/4 (base 6e56487):
// docs/research/shared-retained-complex.md and the new subsection
// "Shared exclusion sums with retained totals" (prop:shared-retained-complex-interface)
// of patches/retained-complex-31.patch. Checked as a separate entry ("pr4b"); the
// earlier head 42a88ef stays pinned as "pr4".
//
// Top-down: the complex producer at h = 24 is PR 3's shared-exclusion side circuit
// (imported verbatim), plus PR 4's two interface changes: retained totals
// E_i = sum_{T not containing i} x_T (i < h-1) and C_* = sum_T x_T replace the central
// wires, and stage-1/stage-3 banks are shared (2 v^2 instead of 3 v^2 invocations
// carry auxiliary roles). Counts: base 66518 additions and 24288 outputs; retention
// activates 120 ancestors and adds 24 outputs: C = 66638, q = 24312, R = 90950.
// Then W = 2N + 2v^2 R, L = 3v^2 ((h-1)^2 + h), D = 2N - 2L, s = Wm - D,
// eta = 365/1285272576, certifying 1 - sigma = 2970/10^11. The bit saving stays
// 296/10^11 and the headline stays kappa = 591/10^12 (bit-limited): this is
// producer headroom, not a larger kappa.

import { q, add, sub, mul, div, lt, eq, twoPow, ONE, show, toDecimal } from "../rational";
import { ground } from "../networks";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { compactParameterChecks, compactMargins, compactMinimumMargin, layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { largestGridSaving } from "../ceiling";
import { BIT_SAVING } from "../checks";
import { tripleList } from "../global";
import { buildComplexCircuit, verifyComplexCircuit, type ComplexCircuit } from "./complexCircuit";
import { pr4Params } from "./pr4";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const DOC = "PR4b shared-retained-complex.md";
const PATCH = "PR4b retained-complex-31.patch prop:shared-retained-complex-interface";
const H = 24;

export const STATED_PR4B = {
  baseAdditions: 66518,
  baseOutputs: 24288,
  newAncestors: 120,
  totals: 24,
  C: 66638,
  q: 24312,
  R: 90950n,
  W: 761750114048n,
  L: 6796219584n,
  D: 2990500480n,
  s: 10530430586099072n,
  eta: q(365n, 1285272576n),
  gates: 3475338442752n,
  L0: q(477n, 50n),
  ac: q(2970n, TEN(11)),
  deficitSlack: q(406952569n, 627574500000000000n),
  ratioOverPR3: q(212n, 100n), // "about 2.12 times PR #3's certified 1.4e-8"
};

export function pr4bParams(): CompactParams {
  const p = pr4Params();
  const ac = q(2970n, TEN(11));
  return { ...p, ac, sigma: sub(ONE, ac) };
}

/** PR 3's circuit at h = 24 with the retained totals; counts and support checks. */
export function computeRetainedShared(h = H) {
  return cached(`pr4b circuit ${h}`, () => analyseRetained(buildComplexCircuit(h, "leftFold", true)));
}

/** Counts and support checks for a circuit built with `retain` (exported so tests can feed corrupted circuits). */
export function analyseRetained(c: ComplexCircuit) {
  {
    const h = c.h;
    const base = verifyComplexCircuit(c);
    const st = c.store;
    const reach = (starts: number[]) => {
      const used = new Uint8Array(st.supports.length);
      const stack = [...starts];
      while (stack.length) {
        const n = stack.pop()!;
        if (n < 0 || used[n]) continue;
        used[n] = 1;
        if (st.left[n]! >= 0) stack.push(st.left[n]!, st.right[n]!);
      }
      return used;
    };
    const baseUsed = reach(c.pieces.map((p) => p.node));
    const totals: number[] = [];
    for (let i = 0; i < h - 1; i++) totals.push(c.retained!.get(1 << i) ?? -1);
    totals.push(c.retained!.get(0) ?? -1);
    const allUsed = reach([...c.pieces.map((p) => p.node), ...totals]);
    let additions = 0;
    let newAncestors = 0;
    for (let n = 0; n < st.supports.length; n++) {
      if (!allUsed[n] || st.left[n]! < 0) continue;
      additions++;
      if (!baseUsed[n]) newAncestors++;
    }
    // supports of the totals, recomputed from the kept additions only, with disjointness
    const triples = tripleList(h);
    const V = triples.length;
    const words = (V + 31) >>> 5;
    const sup = new Map<number, Uint32Array>();
    let disjoint = true;
    for (let n = 0; n < st.supports.length; n++) {
      if (!allUsed[n]) continue;
      const s = new Uint32Array(words);
      if (st.left[n]! < 0) s[n >>> 5]! |= 1 << (n & 31);
      else {
        const l = sup.get(st.left[n]!)!;
        const r = sup.get(st.right[n]!)!;
        for (let w = 0; w < words; w++) {
          if ((l[w]! & r[w]!) !== 0) disjoint = false;
          s[w] = l[w]! | r[w]!;
        }
      }
      sup.set(n, s);
    }
    let totalsExact = totals.every((t) => t >= 0);
    for (let k = 0; k < totals.length && totalsExact; k++) {
      const s = sup.get(totals[k]!)!;
      for (let t = 0; t < V; t++) {
        const want = k === h - 1 ? true : !triples[t]!.includes(k);
        if ((((s[t >>> 5]! >>> (t & 31)) & 1) === 1) !== want) totalsExact = false;
      }
    }
    const plus = c.pieces.filter((p) => p.sign === 1).length;
    return { base, totals, additions, newAncestors, disjoint, totalsExact, distinctTotals: new Set(totals).size === totals.length, plus, minus: c.pieces.length - plus };
  }
}

export function sharedRetainedNetwork(h: number, R: bigint) {
  const { v, N, m } = ground(h);
  const H_ = BigInt(h);
  const ell = (H_ - 1n) ** 2n + H_;
  const W = 2n * N + 2n * v * v * R;
  const L = 3n * v * v * ell;
  const D = 2n * N - 2n * L;
  const s = W * m - D;
  return { v, N, m, ell, W, L, D, s, eta: q(D, W * m) };
}

/** The central scatter (doc): coefficient of source T in target S equals (|S cap T| - 1)/2, for every S, T. */
export function scatterIdentity(h: number) {
  const triples = tripleList(h);
  const last = h - 1;
  let ok = true;
  let sumIdentity = true;
  for (const S of triples) {
    const inS = new Set(S);
    for (const T of triples) {
      const inT = new Set(T);
      const meet = S.filter((x) => inT.has(x)).length;
      // E_i has coefficient 1 on T iff i not in T; C_* has coefficient 1 on every T
      let coef: number;
      if (!inS.has(last)) {
        coef = 1 - 0.5 * S.filter((i) => !inT.has(i)).length; // C_* - (1/2) sum_{i in S} E_i
      } else {
        let k = 0;
        for (let i = 0; i < last; i++) if (!inS.has(i) && !inT.has(i)) k++;
        coef = (5 - h) / 2 + 0.5 * k; // ((5-h)/2) C_* + (1/2) sum_{i < h-1, i not in S} E_i
      }
      if (coef !== (meet - 1) / 2) ok = false; // halves and small integers: exact in binary floating point
    }
    // sum over all h exclusions of the T-coefficient = h - 3 (one source T)
  }
  for (const T of triples) if (Array.from({ length: h }, (_, i) => (T.includes(i) ? 0 : 1)).reduce((a, b) => a + b, 0) !== h - 3) sumIdentity = false;
  return { ok, sumIdentity };
}

export type PR4bOptions = { p?: CompactParams; stated?: Partial<typeof STATED_PR4B> };

export function pr4b(opts: PR4bOptions = {}) {
  const st = { ...STATED_PR4B, ...opts.stated };
  const p = opts.p ?? pr4bParams();
  const out: Result[] = [];
  const r = computeRetainedShared(H);
  const b = r.base;

  // ---- 4bA: base circuit and retention (rebuilt)
  const SA = "PR4b-A PR 3's shared-exclusion circuit at h = 24 with retained totals (rebuilt)";
  const C = BigInt(r.additions);
  const qq = BigInt(b.injections + r.totals.length);
  const R = C + qq;
  out.push(
    equals(SA, "base additions (PR 3's construction at h = 24)", DOC, b.additions, st.baseAdditions),
    equals(SA, "base side outputs", DOC, b.injections, st.baseOutputs),
    truth(SA, "base side map exact at h = 24 (+1/2 on disjoint, -1/2 on intersection-two triples)", "PR3 complex-circuit-construction.tex", b.sideMapExact && b.allAdditionsDisjoint, `${b.nonzeroCoefficients} nonzero coefficients`),
    equals(SA, "zero-output (disjoint) uses = two-output (pair-star) uses = 12144", "certificate producer.zero_output_uses / two_output_uses", `${r.plus}/${r.minus}`, "12144/12144"),
    equals(SA, "retained totals (E_i for i < h-1, and C_*)", DOC, r.totals.length, st.totals),
    truth(SA, "every retained total is exact: E_i = all triples avoiding i, C_* = all triples, each once", DOC + ": Full h24 source coefficients, retained integer multiplicities", r.totalsExact && r.distinctTotals),
    truth(SA, "every kept addition joins disjoint supports (base and retention)", DOC, r.disjoint),
    equals(SA, "newly activated ancestors (additions reachable from the totals, not from the base pieces)", DOC + ": Retention activates 120 additional ancestors", r.newAncestors, st.newAncestors),
    equals(SA, "C = base + activated", DOC, r.additions, st.C),
    equals(SA, "q = base outputs + h", DOC, Number(qq), st.q),
    equals(SA, "R_aux = C + q (the compiler identity applied to the recomputed counts)", DOC, R, st.R, "identity"),
  );
  const sc = cached("pr4b scatter", () => scatterIdentity(H));
  out.push(
    truth(SA, "central scatter: coefficient of T in target S is (|S cap T| - 1)/2 in both cases (all 2024^2 pairs)", DOC + ": Each source coefficient is (|S intersect T|-1)/2", sc.ok),
    truth(SA, "sum of the h exclusion totals = (h - 3) C_* on sources", DOC, sc.sumIdentity, "", "identity"),
    equals(SA, "the coefficient -(h-5)/2 as h - 5 = 19 updates of -1/2: one grouped pass plus h - 6 global passes", DOC, 1 + (H - 6), H - 5, "identity"),
  );

  // ---- 4bB: network counts and the complex saving
  const SB = "PR4b-B network counts, eta, 1 - sigma = 2970/10^11";
  const nw = sharedRetainedNetwork(H, R);
  const logm = cached("pr4 logm", () => logIntegerEnclosure(nw.m, 24));
  const expL0 = cached(`pr4 exp ${show(st.L0)}`, () => expLowerBound(st.L0, 60));
  const enc = savingEnclosure(nw.eta, logm);
  const gates = 3n * nw.v * nw.v * (8n * nw.v + 4n * C + 4n + 2n * BigInt(H - 6));
  out.push(
    equals(SB, "N = v^3", PATCH, nw.N, nw.v ** 3n, "identity"),
    equals(SB, "W = 2N + 2v^2 R_aux", PATCH, nw.W, st.W),
    equals(SB, "L_loss = 3v^2 ((h-1)^2 + h), ell = 553", PATCH, nw.L, st.L),
    equals(SB, "D = 2N - 2 L_loss", PATCH, nw.D, st.D),
    equals(SB, "s = Wm - D", PATCH, nw.s, st.s),
    equals(SB, "eta = D/(Wm) = 365/1285272576", PATCH, nw.eta, st.eta),
    truth(SB, "L_loss < N (positive deficit)", PATCH, nw.L < nw.N),
    fromCheck(SB, { name: "log m < 477/50 (atanh, 24 terms)", source: PATCH, lhs: logm.upper, rel: "<", rhs: st.L0 }),
    truth(SB, "e^(477/50) > m (Taylor partial sum, second route)", PATCH, lt(q(nw.m), expL0)),
    equals(SB, "eta - (2970/10^11)(477/50) = 406952569/627574500000000000", PATCH, sub(nw.eta, mul(st.ac, st.L0)), st.deficitSlack),
    fromCheck(SB, { name: "eta > a_c (477/50), a_c = 2970/10^11", source: PATCH, lhs: mul(st.ac, st.L0), rel: "<", rhs: nw.eta, kind: "implied" }),
    truth(SB, "a_c < lower enclosure of the actual saving -log(1 - eta)/log m (Mercator route)", PATCH, lt(st.ac, enc.lower), `a* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    equals(SB, "gates 3v^2 (8v + 4C + 4 + 2(h-6))", PATCH, gates, st.gates),
    fromCheck(SB, { name: "gates < 12 W", source: PATCH, lhs: q(gates), rel: "<", rhs: q(12n * nw.W) }),
    truth(SB, "a_c / (14/10^9) = 2.12 (to the stated digits)", DOC + ": about 2.12 times PR #3's 1.4e-8", toDecimal(div(st.ac, q(14n, TEN(9))), 2) === toDecimal(st.ratioOverPR3, 2), toDecimal(div(st.ac, q(14n, TEN(9))), 6)),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: PATCH, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "1 - tau <= a_b = 296/10^11 (bit network unchanged)", source: PATCH, lhs: sub(ONE, p.tau), rel: "<=", rhs: BIT_SAVING, kind: "condition" }),
    truth("PR4b-0 observations (not part of the claim)", "largest saving on the 10^-11 grid certified by eta and 477/50", PATCH, true, `${largestGridSaving(nw.eta, st.L0, TEN(11))}/10^11 (stated 2970)`, "observation"),
  );

  // ---- 4bC: guard
  const SC = "PR4b-C generalized guard with the h = 24 shared-retained network (beta = 1/1000, zeta = 1/10000)";
  const gu = compactGuardConstants(nw.W, nw.s, nw.m, p.zeta);
  out.push(...compactGuardChecks(nw.W, nw.s, nw.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SC, k)));
  out.push(fromCheck(SC, { name: "36W^3 + 4s + 4W + 4 < E (depth enclosure; implied by E = 64(W+m+1)^3)", source: DOC, lhs: q(36n * nw.W ** 3n + 4n * nw.s + 4n * nw.W + 4n), rel: "<", rhs: q(gu.E), kind: "implied" }));
  const depth = cached(`pr4b depth ${show(p.beta)} ${nw.s}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], nw.m, nw.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SC, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));

  // ---- 4bD: parameters and margins (kappa unchanged)
  const SD = "PR4b-D compact-control parameters with sigma = 1 - 2970/10^11 (kappa = 591/10^12 unchanged)";
  const x = layerExponents(p);
  const mg = compactMargins(p);
  const G = compactMinimumMargin(p);
  out.push(...compactParameterChecks(p).map((k) => fromCheck(SD, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SD, { name: `kappa < ${k}`, source: PATCH + ": strict consumer comparisons", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SD, "sigma < tau, so chi = tau", PATCH, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SD, "G_* = g3 = 2956521/(5*10^15) (unchanged: no margin depends on sigma)", "README: strict margin/gap remain unchanged", G, q(2956521n, 5n * TEN(15))),
    equals(SD, "G_* - kappa = 1521/(5*10^15)", "README", sub(G, p.kappa), q(1521n, 5n * TEN(15))),
    fromCheck(SD, { name: "kappa > 2^-31", source: "README", lhs: twoPow(-31), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < g3 < eps a < a/5: bit-limited, so the larger a_c does not raise kappa", source: DOC + ": additional producer headroom, not a larger headline exponent", lhs: mg.g3, rel: "<", rhs: div(p.a, q(5n)), kind: "implied" }),
  );

  const OBS = "PR4b-0 observations (not part of the claim)";
  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { circuit: r, network: nw, C, q: qq, R, logm, enclosure: enc, guard: gu, params: p, exponents: x, margins: mg, G, gates } };
}
