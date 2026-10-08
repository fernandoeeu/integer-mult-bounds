// PR 16 (jacklightChen): "Certify nested source-frame batching beyond 2^-20". Head a80f5e6;
// its parent 1051e25 merges PR 13 (3ef246f, which contains PR 10's 62691e3) into main
// 6e56487; a80f5e6 adds research/nested-source/, PR 12's research/ directories at their PR 12
// blobs, notes/nested-bit.tex, notes/nested-complex.tex and patches/nested-source.patch.
// Sources: notes/nested-bit.tex, notes/nested-complex.tex, research/nested-source/README.md.
//
// Top-down.
//  (1) Bit network at h = 32 (v = 201376, m = 32768, H = 1024): producer c = 23210704,
//      Q_out = 2014256, R = 25224960 (PRs 9/11/12's rules; not rebuilt here). PR 7's interface:
//      W = 2v^2(v + R), L = 3v^2 C(h,2)(h-2), s = Wm - N + 2L, eta = 3503/52073136128.
//      Child list with PR 13's source frames, the two data-corner blocks (as in PR 14) and a
//      new nested controlled basis that makes the exit's h-corner diagonal (one block of h):
//        join (B): 64 singletons, 32640;   exit (B): 0 singletons, 32 and 32704;
//        stage-2 data (2N): 63, 898;        stage-3 data (2N): 93, 962 and 30658.
//      S = 167747380096422805504, a_b = 49/25000000 > 2^-19, gap > 3*10^-10.
//  (2) Complex network: PR 7's h = 28 network; every nonzero edge one child; the global
//      histogram is 3v^2 copies of a stated local histogram c_r (r = 1..28) plus five
//      boundary classes. a_c = 4/10^6; guard at rho = 3/2 with an explicit Taylor bound
//      11005895/11035584 < 999/1000; C1 = 3749/2500.
//  (3) Assembly: eps = 499999/10^6, kappa = 9799/10^10 > 2^-20.

import { q, add, sub, mul, div, lt, le, twoPow, ONE, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { type CompactParams } from "../compact/witness";
import { primeFieldBitNetwork, primeFieldComplexNetwork, computeComplex7 } from "./pr7";
import { momentWeights, momentUpperBound, momentUpperSecond, momentLower, logInverseEnclosure, largestGridSaving, type WidthClass } from "./batched";
import { batchedAssemblyRows, ANALYTIC_PR10 } from "./pr10";
import { roleBudget, largestGridConservative, histogramClasses, histogramRankSum, convexPathBound, rhoGuardConstants } from "./allResiduals";
import { equals, truth, fromCheck, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const BIT = "PR16 notes/nested-bit.tex";
const CPX = "PR16 notes/nested-complex.tex";
const README = "PR16 research/nested-source/README.md";

/** nested-complex.tex: the local histogram c_r of one invocation (r = 1..28). */
export const PR16_LOCAL: bigint[] = [
  93912n, 23891n, 21224n, 31667n, 13552n, 9128n, 9240n, 10912n, 5656n, 8456n, 4284n, 7598n, 4872n, 7448n,
  4536n, 7803n, 4228n, 8232n, 4872n, 7482n, 7224n, 5901n, 8400n, 11550n, 1512n, 5180n, 6552n, 87n,
];

export const STATED_PR16 = {
  v: 201376n,
  m: 32768n,
  c: 23210704n,
  Qout: 2014256n,
  R: 25224960n,
  stars: 35960n,
  W: 2062192473897500672n,
  L: 1810254376304640n,
  s: 67573918438923423744000n,
  eta: q(3503n, 52073136128n),
  deficitFraction: q(113n, 203n),
  B: 1022929978317864960n,
  ranks: [32704n, 32736n, 961n, 31713n],
  singles: [64n, 0n, 63n, 93n],
  blocks: "32640;32,32704;898;962,30658",
  S: 167747380096422805504n,
  a: q(49n, 25000000n),
  gapDecimal: q(3n, TEN(10)),
  // complex
  Bc: 1007397164592n,
  Wc: 2085111546336n,
  Dc: 18030055680n,
  sc: 45772350635112192n,
  localSum: 2806804n,
  zeroEdges: 727056n,
  M: 21896n,
  ac: q(4n, TEN(6)),
  cGapDecimal: q(18n, TEN(9)),
  cGapReadme: q(183n, TEN(10)),
  acAlso: q(419n, TEN(8)),
  t: q(1n, 392n),
  y: q(1n, 98n),
  pathBound: q(11005895n, 11035584n),
  C1: q(3749n, 2500n),
  // assembly
  kappa: q(9799n, TEN(10)),
  minMargin: q(4899990199500001n, 5n * TEN(21)),
  agap: q(490199500001n, 5n * TEN(21)),
  overPR13pct: [q(27275n, 1000n), q(27285n, 1000n)] as [Q, Q], // "27.28%"
  overPR14pct: [q(7915n, 1000n), q(7925n, 1000n)] as [Q, Q], // "7.92%"
  over2m20pct: [q(2745n, 1000n), q(2755n, 1000n)] as [Q, Q], // "2.75%"
};

export function pr16Params(): CompactParams {
  const a = STATED_PR16.a;
  const ac = STATED_PR16.ac;
  const tau = sub(ONE, a);
  return {
    a,
    ac,
    tau,
    sigma: sub(ONE, ac),
    epsilon: q(499999n, TEN(6)),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(10)),
    C1: STATED_PR16.C1,
    lambda: add(tau, q(1n, TEN(16))),
    lambdaPrime: add(tau, q(2n, TEN(16))),
    kappa: STATED_PR16.kappa,
  };
}

/** The nested child list (order as in the certificate: join, exit middle, stage-3 middle, stage-2 data, stage-3 corner, exit corner). */
export function pr16Classes(h: bigint, v: bigint, R: bigint, nested = true): WidthClass[] {
  const m = h ** 3n;
  const H = h * h;
  const r = h - 1n;
  const B = v * v * R;
  const N2 = 2n * v ** 3n;
  const out: WidthClass[] = [
    { name: "stage 1-3 join block m - 4h", copies: B, t: m - 4n * h },
    { name: "stage 2 exit middle block m - 2h", copies: B, t: m - 2n * h },
    { name: "stage 3 data middle block m - 2(H + r)", copies: N2, t: m - 2n * (H + r) },
    { name: "stage 2 data entrance block H - 4h + 2", copies: N2, t: H - 4n * h + 2n },
    { name: "stage 3 data corner block H - 2r", copies: N2, t: H - 2n * r },
  ];
  if (nested) out.push({ name: "stage 2 exit diagonal corner block h (nested basis)", copies: B, t: h });
  return out;
}

/** Global histogram: 3v^2 copies of the local c_r plus the five boundary classes. */
export function pr16Histogram(v: bigint, h: bigint, Bc: bigint): Map<bigint, bigint> {
  const m = h ** 3n;
  const N = v ** 3n;
  const hist = new Map<bigint, bigint>();
  const addTo = (r: bigint, c: bigint) => hist.set(r, (hist.get(r) ?? 0n) + c);
  PR16_LOCAL.forEach((c, i) => addTo(BigInt(i + 1), 3n * v * v * c));
  addTo(m - 2n * h, Bc);
  addTo(m - h * h, Bc);
  addTo(h * h - h, Bc);
  addTo((h - 1n) ** 2n, 2n * N);
  addTo((h * h - 1n) * (h - 1n), 2n * N);
  return hist;
}

export function pr16(opts: { p?: CompactParams; stated?: Partial<typeof STATED_PR16> } = {}) {
  const st = { ...STATED_PR16, ...opts.stated };
  const p = opts.p ?? pr16Params();
  const out: Result[] = [];
  const OBS = "PR16-0 observations and analytic steps (not counted)";
  const h = 32n;

  // ---- 16A: bit network at h = 32
  const SA = "PR16-A h = 32 bit network with nested source-frame batching, a_b = 49/25000000 (producer count taken as stated, not rebuilt)";
  const bn = primeFieldBitNetwork(32, st.R);
  const H = h * h;
  const r = h - 1n;
  const qout = binom(h - 2n, 3n) * binom(h, 2n) + binom(h, 2n);
  const cls = pr16Classes(h, bn.v, st.R);
  const ranks = [bn.m - 2n * h, bn.m - h, r * r, (H - 1n) * r];
  const singles = [2n * h, 0n, 2n * h - 1n, 3n * r];
  out.push(
    equals(SA, "v = C(32,5), m = h^3", BIT, `${bn.v},${bn.m}`, `${st.v},${st.m}`),
    equals(SA, "Q_out = C(30,3) C(32,2) + C(32,2)", BIT, qout, st.Qout),
    equals(SA, "R = c + Q_out", BIT, st.c + qout, st.R),
    equals(SA, "stars = C(32,4)", BIT, binom(h, 4n), st.stars, "identity"),
    equals(SA, "W = 2v^2(v + R)", BIT, bn.W, st.W),
    equals(SA, "L = 3v^2 C(h,2)(h - 2)", BIT, bn.L, st.L),
    equals(SA, "s = W m - N + 2L", BIT, bn.s, st.s),
    equals(SA, "eta = (Wm - s)/(Wm)", BIT, bn.eta, st.eta),
    equals(SA, "deficit fraction (N - 2L)/N = 113/203", README, q(bn.N - 2n * bn.L, bn.N), st.deficitFraction),
    equals(SA, "B = v^2 R", BIT, bn.v * bn.v * st.R, st.B),
    equals(SA, "ranks m - 2h, m - h, (h-1)^2, (H-1)(h-1)", BIT, ranks.join(","), st.ranks.join(",")),
    equals(SA, "singletons 2h, 0, 2h - 1, 3(h-1)", BIT, singles.join(","), st.singles.join(",")),
    equals(SA, "blocks m - 4h; h, m - 2h; H - 4h + 2; H - 2(h-1), m - 2(H + h - 1)", BIT, `${cls[0]!.t};${cls[5]!.t},${cls[1]!.t};${cls[3]!.t};${cls[4]!.t},${cls[2]!.t}`, st.blocks),
    truth(SA, "each class: singletons + blocks = rank", BIT, singles[0]! + cls[0]!.t === ranks[0] && cls[5]!.t + cls[1]!.t === ranks[1] && singles[2]! + cls[3]!.t === ranks[2] && singles[3]! + cls[4]!.t + cls[2]!.t === ranks[3]),
    truth(SA, "stage-3 profile 3r + (H - 2r) + (m - 2R') = m - R' = (h-1)(H-1), R' = H + r", BIT, 3n * r + (H - 2n * r) + (bn.m - 2n * (H + r)) === (h - 1n) * (H - 1n), "", "identity"),
    truth(SA, "every child width below m", BIT, cls.every((c) => c.t < bn.m)),
  );
  const w = momentWeights(bn.m, bn.W, bn.s, cls);
  const own = w.items.map((x) => logInverseEnclosure(x.r).upper);
  const b = momentUpperBound(w.items, st.a, own);
  const b2 = momentUpperSecond(w.items, st.a);
  const gridB = cached("pr16 grid bit", () => largestGridSaving(w.items, 25000000n, 49n));
  const gridB9 = cached("pr16 grid bit 1e-9", () => largestGridSaving(w.items, TEN(9), 1960n));
  out.push(
    equals(SA, "S = s - sum_i B_i t_i", BIT, w.S, st.S),
    equals(SA, "weights sum to 1 - eta", BIT, w.total, sub(ONE, st.eta)),
    fromCheck(SA, { name: "sum w_i/(1 - a_b l_i) < 1 - 3/10^10 (own upper enclosures l_i)", source: BIT, lhs: b.bound, rel: "<", rhs: sub(ONE, st.gapDecimal) }),
    fromCheck(SA, { name: "second route: Psi(1 - a_b) < 1", source: "derived", lhs: b2.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "a_b > 2^-19", source: README, lhs: twoPow(-19), rel: "<", rhs: st.a }),
    fromCheck(SA, { name: "1 - tau <= a_b", source: README, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    truth(OBS, "room: largest a_b on the 10^-9 grid (second route)", "derived", true, `${gridB9.k}/10^9 (stated 1960/10^9; Psi >= 1 from ${gridB9.firstFail}/10^9)`, "observation"),
    truth(OBS, "certified bit gap (own logs)", "derived", true, toDecimal(b.gap, 14), "observation"),
  );
  void gridB;
  // what the nested exit corner contributes: without it (h singletons on the exit) a_b fails
  const flat = momentWeights(bn.m, bn.W, bn.s, pr16Classes(h, bn.v, st.R, false));
  out.push(truth(SA, "control: without the nested exit corner block (h singletons per exit), Psi(1 - a_b) >= 1 already by e^x >= 1 + x", BIT, !lt(momentLower(flat.items, st.a), ONE)));
  const gridFlat = cached("pr16 grid flat", () => largestGridSaving(flat.items, TEN(9), 1900n));
  out.push(truth(OBS, "without the nested corner (PR 14's exit profile at h = 32): largest a_b on the 10^-9 grid (second route)", "derived", true, `${gridFlat.k}/10^9`, "observation"));
  const Rmax = cached("pr16 Rmax", () => roleBudget(st.R, st.a, (R) => { const n = primeFieldBitNetwork(32, R); return { m: n.m, W: n.W, s: n.s, classes: pr16Classes(h, n.v, R) }; }));
  out.push(truth(OBS, "role budget: largest R still certifying a_b = 49/25000000 (second route)", "derived", true, `R <= ${Rmax}; stated R = ${st.R} leaves ${Rmax - st.R} roles (${toDecimal(q(Rmax - st.R, st.R), 6)} of R)`, "observation"));

  // ---- 16B: complex network, every residual batched (histogram from the note)
  const SB = "PR16-B complex network at h = 28: every nonzero residual one child (histogram rebuilt from the note's local table), a_c = 4/10^6";
  const cc = computeComplex7();
  const Rc = BigInt(cc.additions + cc.injections);
  const cn = primeFieldComplexNetwork(28, Rc);
  const Bc = cn.v * cn.v * (Rc + 29n);
  const H28 = 28n;
  const localSum = PR16_LOCAL.reduce((acc, c, i) => acc + BigInt(i + 1) * c, 0n);
  const hist = pr16Histogram(cn.v, H28, Bc);
  out.push(
    equals(SB, "B = v^2(R + h + 1)", CPX, Bc, st.Bc),
    equals(SB, "W = 2v^2(v + R + h + 1)", CPX, cn.W, st.Wc),
    equals(SB, "D = 2N - 2L, L = 3v^2 h(h + 1)", CPX, 2n * cn.N - 2n * cn.L, st.Dc),
    equals(SB, "s = Wm - D", CPX, cn.s, st.sc),
    equals(SB, "sum_r r c_r (local table)", CPX, localSum, st.localSum),
    equals(SB, "(2v + R + h + 1)h - 2v + 2h(h + 1)", CPX, (2n * cn.v + Rc + H28 + 1n) * H28 - 2n * cn.v + 2n * H28 * (H28 + 1n), st.localSum),
    equals(SB, "sum_r r H_r = 3v^2 (local sum) + B(21896 + 21168 + 756) + 2N(729 + 21141) = s", CPX, histogramRankSum(hist), cn.s),
    truth(SB, "every rank in [1, M], M = m - 2h < m", CPX, [...hist.keys()].every((x) => x >= 1n && x <= st.M) && st.M === cn.m - 56n),
  );
  const ccl = histogramClasses(hist);
  const cw = momentWeights(cn.m, cn.W, cn.s, ccl);
  const cOwn = cw.items.map((x) => logInverseEnclosure(x.r).upper);
  const c = momentUpperBound(cw.items, st.ac, cOwn);
  const c2 = momentUpperSecond(cw.items, st.ac);
  const cAlso = momentUpperBound(cw.items, st.acAlso, cOwn);
  out.push(
    equals(SB, "weights sum to 1 - D/(Wm)", CPX, cw.total, sub(ONE, q(2n * cn.N - 2n * cn.L, cn.W * cn.m))),
    fromCheck(SB, { name: "sum H_r r/(Wm(1 - a_c l_r)) < 1 at a_c = 4/10^6 (own enclosures)", source: CPX, lhs: c.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "gap > 1.8*10^-8", source: CPX, lhs: st.cGapDecimal, rel: "<", rhs: c.gap }),
    fromCheck(SB, { name: "gap > 1.83*10^-8 (README)", source: README, lhs: st.cGapReadme, rel: "<", rhs: c.gap }),
    fromCheck(SB, { name: "second route: Xi(1 - a_c) < 1", source: "derived", lhs: c2.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "the bound also holds at a_c = 419/10^8", source: CPX, lhs: cAlso.bound, rel: "<", rhs: ONE }),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: README, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "(1 - beta) a_c > a_b (leaf below tau)", source: "derived", lhs: st.a, rel: "<", rhs: mul(sub(ONE, p.beta), st.ac) }),
  );
  const consC = largestGridConservative(cw.items, cOwn, TEN(8), 419n);
  out.push(truth(OBS, "room: largest a_c on the 10^-8 grid (conservative bound with own logs)", "derived", true, `${consC}/10^8`, "observation"));
  out.push(truth(OBS, "zero-rank physical edges per invocation (stated, not checkable here)", CPX, true, `${st.zeroEdges}; global 3v^2 x = ${3n * cn.v * cn.v * st.zeroEdges}`, "observation"));

  // ---- 16C: guard at rho = 3/2
  const SC = "PR16-C path guard for all residual children at rho = 3/2, C1 = 3749/2500";
  const g = convexPathBound(cn.m, H28, st.M);
  const k = rhoGuardConstants(cn.W, cn.m, q(3n, 2n), p.beta, p.zeta);
  out.push(
    equals(SC, "q = m + 6h", CPX, g.qq, 22120n),
    truth(SC, "M < q < 2M", CPX, g.shape),
    equals(SC, "t = (m - M)/m, y = (q - M)/m", CPX, `${show(g.t)},${show(g.y)}`, `${show(st.t)},${show(st.y)}`),
    truth(SC, "(1 - t)^(3/2) <= 1 - 3t/2 + (3/8) t^2/(1 - t) (exact: (1-t)^3 <= T^2)", CPX, g.taylorValid),
    truth(SC, "y^(3/2) < y/9 (y < 1/81)", CPX, g.yNineValid && lt(g.y, q(1n, 81n))),
    equals(SC, "the sum of the two bounds is exactly 11005895/11035584", CPX, g.pr16Bound, st.pathBound),
    fromCheck(SC, { name: "11005895/11035584 < 999/1000", source: CPX, lhs: g.pr16Bound, rel: "<", rhs: q(999n, 1000n) }),
    fromCheck(SC, { name: "path moment below 0.99731 (README)", source: README, lhs: st.pathBound, rel: "<", rhs: q(99731n, 100000n) }),
    fromCheck(SC, { name: "36W^3 + 4s + 4W + 8m + 4 < E", source: CPX, lhs: q(36n * cn.W ** 3n + 4n * cn.s + 4n * cn.W + 8n * cn.m + 4n), rel: "<", rhs: q(k.E) }),
    truth(SC, "at most s nonzero edges (sum of the histogram's copies <= s)", CPX, [...hist.values()].reduce((x, y) => x + y, 0n) <= cn.s),
    truth(SC, "8(2m)^(1/2) <= 16m", CPX, 64n * 2n * cn.m <= (16n * cn.m) ** 2n, "", "constant"),
    truth(SC, "(1 - 999/1000) C_dep >= E", CPX, k.Cdep >= 1000n * k.E, "", "identity"),
    equals(SC, "C1 = 3/2 - beta/2 + zeta", CPX, k.C1, st.C1),
    fromCheck(SC, { name: "eps C1 < 1", source: README, lhs: mul(p.epsilon, p.C1), rel: "<", rhs: ONE }),
    truth(SC, "C0 = ceil(128 m (1 + 1/zeta) C_dep)", CPX, k.C0 > 0n, `C0 = ${k.C0}`, "identity"),
  );

  // ---- 16D: assembly
  const SD = "PR16-D assembly: eps = 499999/10^6, kappa = 9799/10^10";
  const asm = batchedAssemblyRows(SD, p, { gap: st.agap, rho: q(3n, 2n) }, README);
  out.push(...asm.rows);
  const pct = (x: Q) => mul(sub(div(p.kappa, x), ONE), q(100n));
  const inR = (x: Q, [lo, hi]: [Q, Q]) => !lt(x, lo) && lt(x, hi);
  out.push(
    equals(SD, "minimum margin as stated", README, asm.G, st.minMargin),
    fromCheck(SD, { name: "kappa > 2^-20", source: README, lhs: twoPow(-20), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < 2^-19", source: "derived (dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-19), kind: "condition" }),
    truth(SD, "27.28% above PR 13", README, inR(pct(q(7699n, TEN(10))), st.overPR13pct), toDecimal(pct(q(7699n, TEN(10))), 4) + "%"),
    truth(SD, "7.92% above PR 14", README, inR(pct(q(90799n, TEN(11))), st.overPR14pct), toDecimal(pct(q(90799n, TEN(11))), 4) + "%"),
    truth(SD, "2.75% above 2^-20", README, inR(pct(twoPow(-20)), st.over2m20pct), toDecimal(pct(twoPow(-20)), 4) + "%"),
    truth(OBS, "kappa / (a_b/2); PR 15's stated kappa / this kappa", "derived", true, `${toDecimal(div(p.kappa, div(st.a, q(2n))), 7)}; ${toDecimal(div(q(1076678n, TEN(12)), p.kappa), 5)}`, "observation"),
    truth(OBS, "analytic (not checked): lem:nested-source-basis (one rational K_0, J_beta, G_i meeting the A1, A3, A4 and data-entrance conditions, including the diagonal A4 corner, in both orientations), lem:nested-data-entrance-pivots and the A3 corner refinement, and lem:nested-source-interchange", BIT, true, "", "observation"),
    truth(OBS, "analytic (not checked): that the h = 32 producer's source spans are nondegenerate with center dimension 30 and the matching exists at h = 32; the producer count c = 23210704 (not rebuilt; the h = 30 build already exceeded this run's memory)", BIT, true, "", "observation"),
    truth(OBS, "analytic (not checked): that the complex histogram is the complete physical-edge list (local schedules both ways plus five boundary classes), the residual orthonormal bases, the path budget with global frame dimensions and the convexity relaxation", CPX, true, "", "observation"),
    ...ANALYTIC_PR10.map((s) => truth(OBS, `analytic, inherited from PR 10 (not checked): ${s}`, "PR10 notes", true, "", "observation")),
  );
  const ordered = [...out.filter((x) => x.section !== OBS), ...out.filter((x) => x.section === OBS)];
  return { results: ordered, values: { params: p, bit: bn, w, own, b, b2, complex: cn, hist, cw, cOwn, c, c2, guard: { ...g, ...k }, margins: asm.mg, G: asm.G, Rmax, grid: { bit9: gridB9, flat: gridFlat, consC } } };
}
