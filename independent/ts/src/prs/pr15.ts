// PR 15 (eumemic): "Compose smaller h30 source-frame network with full complex batching".
// Head a17cab3, one commit on top of PR 6's head 5015011 (so it contains PRs 3, 5, 6).
// It carries pinned, unmodified copies of PR 10's, PR 12's and PR 13's notes and scripts
// under references/pr10, pr12, pr13, PR 7's network files at their PR 7 blobs, and many
// experiments; the headline is docs/research/source-frame-stream.md with
// certificates/source-frame-stream-witness.json.
// Sources: docs/research/source-frame-stream.md, dimension30-stream.md, batched-stream.md,
// complex-all-residuals.md, current-status.md, README.md.
//
// Top-down.
//  (1) Bit network: a new, smaller h = 30 producer (16 + 14 split, selected local
//      templates, star resynthesis, bilateral nested-wire reuse): 14381873 additions and
//      142941 outputs (14524814 roles), minus 1468002 delivery roles = R = 13056812, center
//      loss C(30,2)(30-2) = 12180, no extra frame loss. PR 7's interface:
//      W = 2v^2(v + R), L = 3v^2 C(h,2)(h-2), s = Wm - N + 2L. PR 13's source-frame classes
//      at h = 30 (join 26880, data entrance 25142, exit 26940). a_b = 2153359/10^12.
//  (2) Complex network: PR 7's h = 28 network unchanged, but every nonzero physical edge
//      (33 distinct ranks) is one whole-residual child: a_c = 4191487/10^12. New guard at
//      rho = 3/2: any path has total rank <= q = m + 6h and parts <= M = m - 2h, so the path
//      moment is at most (M/m)^(3/2) + ((q-M)/m)^(3/2) < 27921787004127/(28*10^12) < 999/1000;
//      C1 = 3/2 - beta/2 + zeta = 3749/2500.
//  (3) Assembly: PR 10's system, c = 1, beta = 1/1000, delta = 10^-10, zeta = 1/10000,
//      eps = (1 - delta)/(2 + a_b) rounded down to 10^-12, kappa = 1076678/10^12 > 2^-20.
// Not rebuilt here: the h = 30 producer (the PR says several GB); the complex rank
// histogram (not stated in any doc; taken from the certificate as an input and checked
// for consistency).

import { q, add, sub, mul, div, lt, le, twoPow, ONE, ZERO, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { type CompactParams } from "../compact/witness";
import { primeFieldBitNetwork, primeFieldComplexNetwork, computeComplex7 } from "./pr7";
import { momentWeights, momentUpperBound, momentUpperSecond, logInverseEnclosure, largestGridSaving, bitClasses } from "./batched";
import { batchedAssemblyRows, STATED_PR10, ANALYTIC_PR10 } from "./pr10";
import { roundedLogUp, roleBudget, largestGridConservative, histogramClasses, histogramRankSum, convexPathBound, rhoGuardConstants } from "./allResiduals";
import { equals, truth, fromCheck, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const SFS = "PR15 docs/research/source-frame-stream.md";
const D30 = "PR15 docs/research/dimension30-stream.md";
const CAR = "PR15 docs/research/complex-all-residuals.md";
const STATUS = "PR15 docs/research/current-status.md / README.md";
const CERT = "PR15 certificates/source-frame-stream-witness.json (input: no doc states it)";

/**
 * The global complex edge-rank histogram (rank -> copies). No PR 15 document states it; it is
 * copied from complex.counts.residual_histogram of the certificate and treated as an input,
 * checked for consistency (rank sum, bulk multiplicities) and against PR 16's histogram.
 */
export const PR15_HISTOGRAM: [bigint, bigint][] = [
  [1n, 3023640337536n], [2n, 769207250448n], [3n, 683339110272n], [4n, 1019567452176n], [5n, 436327347456n], [6n, 293889907584n],
  [7n, 297495918720n], [8n, 351328513536n], [9n, 182103562368n], [10n, 272253840768n], [11n, 137929925952n], [12n, 244629219744n],
  [13n, 156861484416n], [14n, 239799740544n], [15n, 146043451008n], [16n, 251229507984n], [17n, 136126920384n], [18n, 265041818496n],
  [19n, 156861484416n], [20n, 240894422496n], [21n, 232587718272n], [22n, 189991711728n], [23n, 270450835200n], [24n, 371869898400n],
  [25n, 48681150336n], [26n, 166778015040n], [27n, 246110260032n], [28n, 2801097936n], [729n, 105475825728n], [756n, 972238556016n],
  [21141n, 70317217152n], [21168n, 1007397164592n], [21896n, 1007397164592n],
];

export const STATED_PR15 = {
  additions: 14381873n,
  outputs: 142941n,
  embedding: 14524814n,
  removed: 1468002n,
  R: 13056812n,
  centerLoss: 12180n,
  matchingImages: 142506n,
  singles: [60n, 929n, 30n],
  widths: [26880n, 25142n, 26940n],
  a: q(2153359n, TEN(12)),
  // complex
  sc: 45772350635112192n,
  ac: q(4191487n, TEN(12)),
  cGapDecimal: q(134n, TEN(16)),
  pathUpper: q(27921787004127n, 28n * TEN(12)),
  C1: q(3749n, 2500n),
  // assembly
  kappa: q(1076678n, TEN(12)),
  minMargin: q(538339170276524048839n, 5n * TEN(26)),
  agap: q(170276524048839n, 5n * TEN(26)),
  factorAligned: q(538339n, 812n),
  factorAlignedDecimal: "662.979",
  overPR13pct: [q(3975n, 100n), q(3985n, 100n)] as [Q, Q], // README "39.8%", source-frame-stream.md "about 39.85%"
  overPR14pct: [q(1855n, 100n), q(1865n, 100n)] as [Q, Q], // "18.6%"
};

/** eps = (1 - delta)/(2 + a_b), rounded down to the 10^-12 grid (source-frame-stream.md). */
export const pr15Epsilon = (a: Q, delta: Q) => {
  const x = div(sub(ONE, delta), add(q(2n), a));
  return q((x.num * TEN(12)) / x.den, TEN(12));
};

export function pr15Params(): CompactParams {
  const a = STATED_PR15.a;
  const ac = STATED_PR15.ac;
  const tau = sub(ONE, a);
  const delta = q(1n, TEN(10));
  return {
    a,
    ac,
    tau,
    sigma: sub(ONE, ac),
    epsilon: pr15Epsilon(a, delta),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta,
    C1: STATED_PR15.C1,
    lambda: add(tau, q(1n, TEN(16))),
    lambdaPrime: add(tau, q(2n, TEN(16))),
    kappa: STATED_PR15.kappa,
  };
}

export function pr15(opts: { p?: CompactParams; stated?: Partial<typeof STATED_PR15>; histogram?: [bigint, bigint][] } = {}) {
  const st = { ...STATED_PR15, ...opts.stated };
  const p = opts.p ?? pr15Params();
  const hist = new Map(opts.histogram ?? PR15_HISTOGRAM);
  const out: Result[] = [];
  const OBS = "PR15-0 observations and analytic steps (not counted)";
  const H = 30n;

  // ---- 15A: bit network
  const SA = "PR15-A smaller h = 30 bit network with PR 13's source frames, a_b = 2153359/10^12 (producer count taken as stated, not rebuilt)";
  const bn = primeFieldBitNetwork(30, st.R);
  const cl = bitClasses(H, bn.v, st.R, "sourceFrames");
  const rk = cl.ranks as { a1: bigint; a3: bigint; a4: bigint };
  out.push(
    equals(SA, "retained additions + designated outputs = binary-embedding roles", D30, st.additions + st.outputs, st.embedding),
    equals(SA, "roles = embedding roles - removed delivery roles", D30, st.embedding - st.removed, st.R),
    equals(SA, "designated outputs = v + C(h,2) (one per five-set plus the pair totals)", D30, bn.v + binom(H, 2n), st.outputs),
    equals(SA, "center loss C(h,2)(h - 2)", D30, binom(H, 2n) * (H - 2n), st.centerLoss),
    equals(SA, "matching images = v = C(30,5)", D30, bn.v, st.matchingImages, "identity"),
    equals(SA, "singleton pivots: join 2h, data entrance m - (H-1)(h-1), exit h", SFS, `${bn.m - rk.a1},${bn.m - rk.a3},${bn.m - rk.a4}`, st.singles.join(",")),
    equals(SA, "block widths m - 4h, 2(H-1)(h-1) - m, m - 2h", SFS, cl.classes.map((c) => c.t).join(","), st.widths.join(",")),
    truth(SA, "entrance + exit ranks unchanged: (h^2 - h) + (m - h^2) = m - h", SFS, H * H - H + (bn.m - H * H) === bn.m - H, "", "identity"),
  );
  const w = momentWeights(bn.m, bn.W, bn.s, cl.classes);
  const own = w.items.map((x) => logInverseEnclosure(x.r).upper);
  const ells9 = w.items.map((x) => roundedLogUp(x.r, TEN(9)));
  const b = momentUpperBound(w.items, st.a, own);
  const b9 = momentUpperBound(w.items, st.a, ells9);
  const b2 = momentUpperSecond(w.items, st.a);
  out.push(
    equals(SA, "weights sum to 1 - eta (rank sum unchanged)", SFS, w.total, sub(ONE, bn.eta), "identity"),
    fromCheck(SA, { name: "Psi(1 - a_b) <= sum w_i/(1 - a_b l_i) < 1 with this checker's own upper enclosures l_i", source: SFS, lhs: b.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "the same with l_i rounded up to 10^-9 (dimension30-stream.md's rounding)", source: D30, lhs: b9.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "second route: Psi(1 - a_b) < 1 (sharper exponential bound)", source: "derived", lhs: b2.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "1 - tau <= a_b", source: SFS, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
  );
  const consOwn = largestGridConservative(w.items, own, TEN(12), 2153359n);
  const cons9 = largestGridConservative(w.items, ells9, TEN(12), 2153359n);
  const gridB = cached("pr15 grid bit", () => largestGridSaving(w.items, TEN(12), 2153359n));
  out.push(
    truth(OBS, "'the next grid point fails the conservative moment bound': largest a_b on the 10^-12 grid with 1/(1-x) and logs rounded to 10^-9; with own unrounded logs; second route", SFS, true, `${cons9}/10^12; ${consOwn}/10^12; ${gridB.k}/10^12`, "observation"),
    truth(OBS, "certified bit gap (own logs; logs rounded to 10^-9)", "derived", true, `${toDecimal(b.gap, 18)}; ${toDecimal(b9.gap, 18)}`, "observation"),
  );
  const Rmax = cached("pr15 Rmax", () => roleBudget(st.R, st.a, (R) => { const n = primeFieldBitNetwork(30, R); return { m: n.m, W: n.W, s: n.s, classes: bitClasses(H, n.v, R, "sourceFrames").classes }; }));
  out.push(truth(OBS, "role budget: largest R still certifying a_b = 2153359/10^12 (second route)", "derived", true, `R <= ${Rmax}; stated R = ${st.R} leaves ${Rmax - st.R} roles (${toDecimal(q(Rmax - st.R, st.R), 7)} of R)`, "observation"));
  // the stated physical rank sums are consistent with a formula fitted here (not stated by the PR)
  const fit = (h: bigint, v: bigint, R: bigint) => (v + R) * h + (h - 2n) * v + 2n * binom(h, 2n) * (h - 2n);
  out.push(truth(OBS, "physical rank sum per invocation 399994068 (h = 30) and 250925864 (h = 28, R = 8771396) both equal (v + R)h + (h-2)v + 2 C(h,2)(h-2), a formula fitted here, not stated by the PR", D30 + "; batched-stream.md", fit(30n, bn.v, st.R) === 399994068n && fit(28n, binom(28n, 5n), 8771396n) === 250925864n, `${fit(30n, bn.v, st.R)}, ${fit(28n, binom(28n, 5n), 8771396n)}`, "observation"));

  // ---- 15B: complex network, every residual batched
  const SB = "PR15-B complex network: every nonzero residual one child (histogram from the certificate), a_c = 4191487/10^12";
  const cc = computeComplex7();
  const Rc = BigInt(cc.additions + cc.injections);
  const cn = primeFieldComplexNetwork(28, Rc);
  const Bc = cn.v * cn.v * (Rc + 29n);
  const ranks = [...hist.keys()];
  const M = ranks.reduce((x, y) => (x > y ? x : y), 0n);
  const ccl = histogramClasses(hist);
  const cw = momentWeights(cn.m, cn.W, cn.s, ccl);
  out.push(
    equals(SB, "complex s (PR 7's network, R_c = 93838 rebuilt in entry 7)", CAR, cn.s, st.sc),
    equals(SB, "sum over the histogram of rank x copies = s", CAR, histogramRankSum(hist), cn.s),
    equals(SB, "singleton class S = s - sum_{r >= 2} r H_r equals H_1", CAR, cw.S, hist.get(1n) ?? 0n),
    equals(SB, "bulk multiplicities: ranks m - 2h and m - h^2 have B_c = v^2(R_c + h + 1) copies", CAR, `${hist.get(cn.m - 56n)},${hist.get(cn.m - 784n)}`, `${Bc},${Bc}`),
    equals(SB, "stage-three data entrance rank (h^2-1)(h-1) has 2 v^3 copies", CAR, hist.get(21141n) ?? 0n, 2n * cn.v ** 3n),
    truth(SB, "every rank in [1, m): all residuals proper (no rank-m exception)", CAR, ranks.every((r) => r >= 1n && r < cn.m)),
    equals(SB, "maximum rank M = m - 2h", CAR, M, cn.m - 56n),
    equals(SB, "weights sum to 1 - eta_c", CAR, cw.total, sub(ONE, cn.eta), "identity"),
  );
  const cOwn = cw.items.map((x) => logInverseEnclosure(x.r).upper);
  const c = momentUpperBound(cw.items, st.ac, cOwn);
  const c2 = momentUpperSecond(cw.items, st.ac);
  out.push(
    fromCheck(SB, { name: "Xi(1 - a_c) <= sum w/(1 - a_c l) < 1 with own enclosures", source: CAR, lhs: c.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "strict gap > 1.34*10^-14", source: CAR, lhs: st.cGapDecimal, rel: "<", rhs: c.gap }),
    fromCheck(SB, { name: "second route: Xi(1 - a_c) < 1", source: "derived", lhs: c2.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: SFS, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "(1 - beta) a_c > a_b (leaf below tau)", source: "derived", lhs: st.a, rel: "<", rhs: mul(sub(ONE, p.beta), st.ac) }),
  );
  const gridC = cached("pr15 grid c", () => largestGridSaving(cw.items, TEN(12), 4191487n));
  const consC = largestGridConservative(cw.items, cOwn, TEN(12), 4191487n);
  out.push(
    truth(OBS, "room: largest a_c on the 10^-12 grid (conservative with own logs; second route)", CAR, true, `${consC}/10^12; ${gridC.k}/10^12`, "observation"),
    truth(OBS, "the doc says 'the executable schedule counts 34 residual ranks'; the certificate's histogram has 33 nonzero ranks (34 only if rank 0 is counted)", CAR, true, `${hist.size} nonzero ranks`, "observation"),
  );

  // ---- 15C: rho = 3/2 guard
  const SC = "PR15-C path guard for all residual children at rho = 3/2, C1 = 3749/2500";
  const g = convexPathBound(cn.m, 28n, M);
  const k = rhoGuardConstants(cn.W, cn.m, q(3n, 2n), p.beta, p.zeta);
  out.push(
    equals(SC, "q = m + 6h", CAR, g.qq, 22120n),
    truth(SC, "M < q < 2M (the convex relaxation's extremal list is (M, q - M))", CAR, g.shape),
    fromCheck(SC, { name: "(M/m)^(3/2) + ((q-M)/m)^(3/2) < 27921787004127/(28*10^12) (exact upper square roots)", source: CAR, lhs: g.sharp, rel: "<", rhs: st.pathUpper }),
    fromCheck(SC, { name: "27921787004127/(28*10^12) < 999/1000", source: CAR, lhs: st.pathUpper, rel: "<", rhs: q(999n, 1000n) }),
    fromCheck(SC, { name: "36W^3 + 4s + 4W + 8m + 4 < E = 64(W + m + 1)^3 (complex W, s)", source: CAR, lhs: q(36n * cn.W ** 3n + 4n * cn.s + 4n * cn.W + 8n * cn.m + 4n), rel: "<", rhs: q(k.E) }),
    truth(SC, "at most s nonzero edges, so 4 wrapper operations per edge fit the 4s allowance (sum of copies <= s)", CAR, [...hist.values()].reduce((x, y) => x + y, 0n) <= cn.s),
    truth(SC, "leaf: 8 (2m)^(1/2) <= 16m, i.e. 64 (2m) <= (16m)^2", CAR, 64n * 2n * cn.m <= (16n * cn.m) ** 2n, "", "constant"),
    truth(SC, "induction gap: (1 - 999/1000) C_dep >= E", CAR, k.Cdep >= 1000n * k.E, "", "identity"),
    equals(SC, "C1 = 3/2 - beta/2 + zeta", CAR, k.C1, st.C1),
    fromCheck(SC, { name: "eps C1 < 1", source: CAR, lhs: mul(p.epsilon, p.C1), rel: "<", rhs: ONE }),
    truth(SC, "C0 = ceil(128 m (1 + 1/zeta) C_dep)", CAR, k.C0 > 0n, `C0 = ${k.C0}`, "identity"),
  );

  // ---- 15D: assembly
  const SD = "PR15-D assembly: eps = (1 - delta)/(2 + a_b) rounded down to 10^-12, kappa = 1076678/10^12";
  const asm = batchedAssemblyRows(SD, p, { gap: st.agap, rho: q(3n, 2n) }, SFS);
  out.push(...asm.rows);
  const pct13 = mul(sub(div(p.kappa, q(7699n, TEN(10))), ONE), q(100n));
  const pct14 = mul(sub(div(p.kappa, q(90799n, TEN(11))), ONE), q(100n));
  out.push(
    equals(SD, "minimum margin as stated", SFS, asm.G, st.minMargin),
    truth(SD, "eps is on the 10^-12 grid and (1 - delta)/(2 + a_b) - eps < 10^-12", SFS, (() => { const x = div(sub(ONE, p.delta), add(q(2n), st.a)); return le(p.epsilon, x) && lt(sub(x, p.epsilon), q(1n, TEN(12))); })(), show(p.epsilon)),
    fromCheck(SD, { name: "kappa > 2^-20", source: STATUS, lhs: twoPow(-20), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < 2^-19", source: "derived (dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-19), kind: "condition" }),
    equals(SD, "factor over the aligned-bit 1624/10^12 = 538339/812", SFS, div(p.kappa, q(1624n, TEN(12))), st.factorAligned),
    truth(SD, "538339/812 is about 662.979", SFS, toDecimal(st.factorAligned, 3) === st.factorAlignedDecimal, toDecimal(st.factorAligned, 6)),
    truth(SD, "39.8% (about 39.85%) above PR 13", STATUS, !lt(pct13, st.overPR13pct[0]) && lt(pct13, st.overPR13pct[1]), toDecimal(pct13, 4) + "%"),
    truth(SD, "18.6% above PR 14", STATUS, !lt(pct14, st.overPR14pct[0]) && lt(pct14, st.overPR14pct[1]), toDecimal(pct14, 4) + "%"),
    truth(OBS, "kappa / (a_b/2)", "derived", true, toDecimal(div(p.kappa, div(st.a, q(2n))), 7), "observation"),
    truth(OBS, "analytic (not checked): that bilateral nested-wire reuse leaves every auxiliary's boundary frames, the center loss and the source-frame endpoints unchanged (so PR 13's lemma and the controlled basis apply to the reused registers), and the 60-node delayed source cut", D30, true, "", "observation"),
    truth(OBS, "analytic (not checked): the whole-residual identity on every edge (orthonormal residual bases for all 33 ranks), that the histogram is the complete physical-edge list of the compiled schedule, the path budget q = m + 6h with global frame dimensions, and the convexity relaxation", CAR, true, "", "observation"),
    truth(OBS, "not rebuilt here: the h = 30 producer (14381873 additions, ZDD support audit, physical allocator), the 142506-image matching, the frame audit and the small basis controls; the complex histogram (input from the certificate)", D30, true, "", "observation"),
    ...ANALYTIC_PR10.map((s) => truth(OBS, `analytic, inherited from PR 10 (not checked): ${s}`, "PR10 notes", true, "", "observation")),
  );
  const ordered = [...out.filter((x) => x.section !== OBS), ...out.filter((x) => x.section === OBS)];
  return { results: ordered, values: { params: p, bit: bn, w, own, ells9, b, b9, b2, complex: cn, hist, cw, cOwn, c, c2, guard: { ...g, ...k }, margins: asm.mg, G: asm.G, Rmax, grid: { cons9, consOwn, bit: gridB, consC, complex: gridC } } };
}
