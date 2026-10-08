// PR 12 (Rohan Arun): "Combine dimension-30 geometry with controlled batching for
// conditional kappa 1.2649e-7". Head 35d31e3 on top of PR 10's commit 62691e3; it also
// contains PR 9's and PR 11's research directories byte-identically (same blobs).
// Sources: research/batched-followup/README.md and proof.tex, and the 08-assembly hunk of
// patches/batched-dimension30.patch.
//
// Top-down: PR 10's controlled batching applied to a bit network at h = 30 (PR 11's
// dimension screen, with PR 9's star rules and PR 11's matching) instead of h = 28.
//   v = C(30,5) = 142506, m = 27000, c = 16089992, Q = 1425495, R = 17515487,
//   W = 2v^2(v + R), L = 3v^2 C(h,2)(h-2), s = Wm - N + 2L, eta = 3857/52973979000.
//   Classes (B = v^2 R): join rank 26940 (60 singletons, block 26880); sink rank 26100
//   (blocks 25200 and 900); data entrance (2N copies) rank 26071 (929 singletons, block
//   25142). S_1 = 373570603170925665960; Psi(1 - 253/10^9) < 1 with gap > 9*10^-12.
// The complex network and guard stay PR 10's (h = 28, a_c = 7/10^7). Assembly: PR 10's
// system with eps = 49999993/10^8, kappa = 12649/10^11.
// Not rebuilt here: the h = 30 producer (c = 16089992); the PR says it needs several GB.

import { q, add, sub, mul, div, lt, twoPow, ONE, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { type CompactParams } from "../compact/witness";
import { primeFieldBitNetwork } from "./pr7";
import { momentWeights, momentUpperBound, momentUpperSecond, logInverseEnclosure, largestGridSaving, bitClasses } from "./batched";
import { batchedAssemblyRows, STATED_PR10, ANALYTIC_PR10 } from "./pr10";
import { equals, truth, fromCheck, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const PROOF = "PR12 research/batched-followup/proof.tex";
const README = "PR12 research/batched-followup/README.md";
const ASM = "PR12 batched-dimension30.patch 08-assembly";
const H = 30n;

export const STATED_PR12 = {
  v: 142506n,
  m: 27000n,
  c: 16089992n,
  Q: 1425495n,
  R: 17515487n,
  eta: q(3857n, 52973979000n),
  ranks: [26940n, 26100n, 26071n],
  singles: [60n, 0n, 929n],
  blocks: "26880;25200,900;25142",
  S1: 373570603170925665960n,
  a: q(253n, TEN(9)),
  gapDecimal: q(9n, TEN(12)),
  stars: 27405n,
  matchingImages: 142506n,
  table: [
    q(999999747n, TEN(9)), q(253n, TEN(9)), q(9999993n, TEN(7)), q(7n, TEN(7)), q(1n), q(49999993n, TEN(8)), q(1n, 1000n), q(999n, 1000n),
    q(1n, TEN(16)), q(4470000001n, TEN(16)), q(2529999999n, TEN(16)), q(1n, TEN(16)), q(1n, TEN(16)), q(2231500001n, 5n * TEN(15)), q(1264999999n, 5n * TEN(15)),
    q(400050083993n, TEN(12)), q(12650001771n, TEN(17)), q(7n, 50000000n), q(5000000699n, TEN(10)), q(1n, TEN(10)), q(1249999999n, TEN(10)),
    q(7n, 50000000n), q(7n, 50000000n), q(49999993n, TEN(8)), q(50000007n, TEN(8)), q(12649n, TEN(11)), q(1399n, TEN(10)), q(7n, 50000000n),
    q(4999998735000001n, 5n * TEN(15)),
  ],
  margins: {
    g1: q(7n, 50000000n),
    g2: q(12649998229n, TEN(17)),
    g3: q(63249991095000007n, 5n * TEN(23)),
    g4: q(12650001771n, TEN(17)),
    g5: q(1399n, TEN(10)),
    g6: q(5000000699n, TEN(10)),
    g7: q(49999993n, TEN(8)),
  } as Record<string, Q>,
  gap: q(4991095000007n, 5n * TEN(23)),
  gapReadme: q(998219n, TEN(17)), // "approximately 9.98219e-12"
  leafGap: q(6993n, TEN(10)),
  epsC1: q(599949916007n, TEN(12)),
  alphaExp: q(50000007n, 200000000n),
  primeExp: q(7n, 50000000n),
};

export function pr12Params(): CompactParams {
  const a = q(253n, TEN(9));
  const ac = q(7n, TEN(7));
  const tau = sub(ONE, a);
  return {
    a,
    ac,
    tau,
    sigma: sub(ONE, ac),
    epsilon: q(49999993n, TEN(8)),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(10)),
    C1: q(11999n, 10000n),
    lambda: add(tau, q(1n, TEN(16))),
    lambdaPrime: add(tau, q(2n, TEN(16))),
    kappa: q(12649n, TEN(11)),
  };
}

/** Upper bounds rounded up to a multiple of 10^-9, as the proof describes ("rounding each upper enclosure upward"). */
const roundedLog = (r: Q) => {
  const u = logInverseEnclosure(r).upper;
  return q((u.num * TEN(9) + u.den - 1n) / u.den, TEN(9));
};

export function pr12(opts: { p?: CompactParams; stated?: Partial<typeof STATED_PR12> } = {}) {
  const st = { ...STATED_PR12, ...opts.stated };
  const p = opts.p ?? pr12Params();
  const out: Result[] = [];
  const OBS = "PR12-0 observations and analytic steps (not counted)";

  const SA = "PR12-A bit network at h = 30: counts, eta, the three classes (producer count taken as stated)";
  const bn = primeFieldBitNetwork(Number(H), st.R);
  const qq = binom(H - 2n, 3n) * binom(H, 2n) + binom(H, 2n);
  const cl = bitClasses(H, bn.v, st.R, "controlled");
  out.push(
    equals(SA, "v = C(30,5)", PROOF, bn.v, st.v),
    equals(SA, "m = h^3", PROOF, bn.m, st.m),
    equals(SA, "Q = C(28,3) C(30,2) + C(30,2) (2600-analogue outputs per pair plus the retained total)", PROOF, qq, st.Q),
    equals(SA, "R = c + Q", PROOF, st.c + qq, st.R),
    equals(SA, "stars = C(30,4)", PROOF, binom(H, 4n), st.stars, "identity"),
    equals(SA, "eta = (Wm - s)/(Wm) with W = 2v^2(v+R), L = 3v^2 C(h,2)(h-2)", PROOF, bn.eta, st.eta),
    truth(SA, "2L < N (positive deficit)", PROOF, 2n * bn.L < bn.N),
    equals(SA, "ranks m - 2h, m - h^2, (h^2-1)(h-1)", PROOF, `${cl.ranks.a1},${cl.ranks.a2},${cl.ranks.a3}`, st.ranks.join(",")),
    equals(SA, "singleton pivots (the sink has none: diagonal corner)", PROOF, `${bn.m - cl.ranks.a1},0,${bn.m - cl.ranks.a3}`, st.singles.join(",")),
    equals(SA, "block widths", PROOF, `${cl.classes[0]!.t};${cl.classes[1]!.t},${cl.classes[3]!.t};${cl.classes[2]!.t}`, st.blocks),
    truth(SA, "2(H + h - 1) < hH (the controlled corner index sets are disjoint at h = 30)", PROOF, 2n * (H * H + H - 1n) < H * H * H, "", "constant"),
  );
  const w = momentWeights(bn.m, bn.W, bn.s, cl.classes);
  const ells = w.items.map((x) => roundedLog(x.r));
  const b = momentUpperBound(w.items, st.a, ells);
  const b2 = momentUpperSecond(w.items, st.a);
  const grid = cached("pr12 grid", () => largestGridSaving(w.items, TEN(9), 253n));
  out.push(
    equals(SA, "S_1 = s - B(26880 + 25200 + 900) - 2N 25142", PROOF, w.S, st.S1),
    equals(SA, "weights sum to 1 - eta", PROOF, w.total, sub(ONE, bn.eta), "identity"),
    fromCheck(SA, { name: "Psi(1 - 253/10^9) <= sum w_i/(1 - a l_i) < 1 (l_i: own upper enclosures rounded up to 10^-9)", source: PROOF, lhs: b.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "1 - certified upper bound > 9*10^-12", source: PROOF + "; " + README, lhs: st.gapDecimal, rel: "<", rhs: b.gap }),
    fromCheck(SA, { name: "second route: Psi(1-a) < 1 (sharper exponential bound)", source: "derived", lhs: b2.bound, rel: "<", rhs: ONE }),
    fromCheck(SA, { name: "1 - tau <= a_b", source: ASM, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    truth(OBS, "room: largest a_b on the 10^-9 grid (second route)", "derived", true, `${grid.k}/10^9 (Psi >= 1 from ${grid.firstFail}/10^9)`, "observation"),
    truth(OBS, "certified gap with the rounded logs", "derived", true, toDecimal(b.gap, 16), "observation"),
  );
  // role budget: how large could R be with a_b = 253/10^9 still certified?
  const Rmax = cached("pr12 Rmax", () => {
    let lo = st.R;
    let hi = st.R * 2n;
    const ok = (R: bigint) => {
      const n = primeFieldBitNetwork(Number(H), R);
      const ww = momentWeights(n.m, n.W, n.s, bitClasses(H, n.v, R, "controlled").classes);
      return momentUpperSecond(ww.items, st.a).bound.num < momentUpperSecond(ww.items, st.a).bound.den;
    };
    if (!ok(lo)) return lo - 1n;
    while (hi - lo > 1n) {
      const mid = (lo + hi) / 2n;
      if (ok(mid)) lo = mid;
      else hi = mid;
    }
    return lo;
  });
  out.push(truth(OBS, "role budget: largest R still certifying a_b = 253/10^9 (second route)", "derived", true, `R <= ${Rmax}; stated R = ${st.R} leaves ${Rmax - st.R} roles (${toDecimal(q(Rmax - st.R, st.R), 6)} of R)`, "observation"));

  const SB = "PR12-B assembly: PR 10's system with eps = 49999993/10^8, kappa = 12649/10^11 (complex network and guard unchanged from PR 10, entry 10)";
  const asm = batchedAssemblyRows(SB, p, { table: st.table, margins: st.margins, gap: st.gap, leafGap: st.leafGap }, ASM);
  out.push(...asm.rows);
  out.push(
    fromCheck(SB, { name: "1 - sigma <= a_c = 7/10^7 (PR 10's complex saving, entry 10)", source: ASM, lhs: sub(ONE, p.sigma), rel: "<=", rhs: STATED_PR10.ac, kind: "condition" }),
    equals(SB, "eps C1", ASM, mul(p.epsilon, p.C1), st.epsC1),
    equals(SB, "alpha exponent (1 - eps)/2", ASM, div(sub(ONE, p.epsilon), q(2n)), st.alphaExp),
    equals(SB, "prime-interval ratio exponent 1 - 2 eps", ASM, sub(ONE, mul(q(2n), p.epsilon)), st.primeExp),
    truth(SB, "G_* - kappa = 9.98219e-12 (README, to the stated digits)", README, toDecimal(sub(asm.G, p.kappa), 17) === toDecimal(st.gapReadme, 17), toDecimal(sub(asm.G, p.kappa), 20)),
    fromCheck(SB, { name: "kappa > 2^-23", source: ASM, lhs: twoPow(-23), rel: "<", rhs: p.kappa, kind: "condition" }),
    truth(SB, "kappa is about 2.84% larger than PR 10's 6149999/(5*10^13) (rounds to 2.84: in [2.835, 2.845))", README, (() => { const pct = mul(sub(div(p.kappa, STATED_PR10.table[25]!), ONE), q(100n)); return !lt(pct, q(2835n, 1000n)) && lt(pct, q(2845n, 1000n)); })(), toDecimal(mul(sub(div(p.kappa, STATED_PR10.table[25]!), ONE), q(100n)), 4) + "%"),
    truth(OBS, "kappa / (a_b/2)", "derived", true, toDecimal(div(p.kappa, div(st.a, q(2n))), 7), "observation"),
    truth(OBS, "not rebuilt here: the h = 30 producer count c = 16089992 (exact support merging at h = 30, 456 templates under PR 9's rules), the 142506-image matching, the template F3 checks", PROOF, true, "the h = 28 build already needs about 1.8 GB; h = 30 is larger than this run's memory budget", "observation"),
    ...ANALYTIC_PR10.map((s) => truth(OBS, `analytic, inherited from PR 10 (not checked): ${s}`, "PR10 notes", true, "", "observation")),
    truth(OBS, "analytic (not checked): that the controlled-basis lemma and the frame schedule carry over to h = 30 (proof.tex argues they do not use h = 28 or the parity of h/2) and that a bit network at h = 30 combines with a complex network at h = 28", PROOF, true, "", "observation"),
  );
  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { params: p, bit: bn, Q: qq, w, ells, b, b2, grid, Rmax, margins: asm.mg, G: asm.G } };
}
