// PR 9 (Rohan Arun): "Refine attributed ternary star templates for conditional kappa
// 3.8e-9". Head cfd6a2b, base 6e56487. Adds research/prime-field-followup/ only; PR 7's
// scripts and certificate are vendored byte-identically (vendor/ blobs equal prs/7's).
// Sources: research/prime-field-followup/README.md (the claim and the rule),
// star_duality.py and verify.py (the exact tie order and the candidate set).
//
// Top-down: PR 7's construction with one change. Each of PR 7's 365 canonical star
// templates is re-synthesized by three rules (PR 7's published greedy; "large first":
// on equal pair frequency prefer the larger union support, then ascending union mask;
// the same with descending masks), unused gates are pruned, and the smallest circuit is
// kept. Star additions 3006276 -> 2452660 (PR 7: 2623060), c = 10687362, q = 983178,
// R = 11670540, eta_b = 117/1537792480 > (761/10^11) log m, a_b = 761/10^11. The complex
// network (a_c = 39/10^9) and PR 7's fast-Gaussian assembly are kept with new numbers:
// lambda = 1 - 7609/10^12, lambda' = 1 - 7608/10^12, kappa = 19/(5*10^9);
// G_* = 4754049/(125*10^13), gap 4049/(125*10^13).

import { q, add, sub, mul, div, lt, eq, twoPow, ONE, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { fastParameterChecks, fastMargins, fastMinimumMargin } from "./fastGaussian";
import { primeFieldBitNetwork, primeFieldComplexNetwork, computeGlobal7, computeComplex7, largestR, STATED_PR7 } from "./pr7";
import { checkTemplate } from "./primeField";
import { largeFirstGreedy } from "./starRules";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const README = "PR9 research/prime-field-followup/README.md";
const H = 28;

export const STATED_PR9 = {
  oldStar: 3006276,
  pr7Star: 2623060,
  newStar: 2452660,
  saved: 170400,
  c: 10687362n,
  q: 983178n,
  R: 11670540n,
  templates: 365,
  stars: 20475,
  eta: q(117n, 1537792480n),
  a: q(761n, TEN(11)),
  L0: q(9997n, 1000n),
  G: q(4754049n, 1250000000000000n),
  gap: q(4049n, 1250000000000000n),
  Gdecimal: "0.0000000038032392",
  ratio: "1.88", // 380/373 - 1, "approximately 1.88%"
};

export function pr9Params(): CompactParams {
  const a = q(761n, TEN(11));
  const ac = q(39n, TEN(9));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(4999n, 10000n),
    c: q(9999n, 10000n),
    beta: q(19n, 25n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(19601n, 10000n),
    lambda: sub(ONE, q(7609n, TEN(12))),
    lambdaPrime: sub(ONE, q(7608n, TEN(12))),
    kappa: q(19n, 5n * TEN(9)),
  };
}

/** Re-synthesize every template of PR 7's global build with the three candidates. */
export function computeStars9() {
  return cached("pr9 stars", () => {
    const G = computeGlobal7();
    let newStar = 0;
    let allValid = true;
    let winners = { published: 0, large: 0, largeReverse: 0 };
    let largeOnly = 0;
    let largeRevOnly = 0;
    for (const t of G.templateList) {
      const L = largeFirstGreedy(t.targets, false);
      const LR = largeFirstGreedy(t.targets, true);
      const width = H - 4;
      if (!checkTemplate(width, t.targets, L) || !checkTemplate(width, t.targets, LR)) allValid = false;
      const best = Math.min(t.published, L.length, LR.length);
      newStar += t.uses * best;
      largeOnly += t.uses * Math.min(t.published, L.length);
      largeRevOnly += t.uses * Math.min(t.published, LR.length);
      if (best === L.length) winners.large++;
      else if (best === LR.length) winners.largeReverse++;
      else winners.published++;
    }
    return { G, newStar, allValid, winners, largeOnly, largeRevOnly };
  });
}

export function pr9(opts: { p?: CompactParams; stated?: Partial<typeof STATED_PR9> } = {}) {
  const st = { ...STATED_PR9, ...opts.stated };
  const p = opts.p ?? pr9Params();
  const out: Result[] = [];
  const OBS = "PR9-0 observations (not part of the claim)";

  const SA = "PR9-A star re-synthesis on PR 7's 365 templates (PR 7's global producer rebuilt in entry 7)";
  const s = computeStars9();
  const G = s.G;
  const c = BigInt(G.unique - G.oldStar + s.newStar);
  const qq = BigInt(G.roots);
  out.push(
    equals(SA, "templates", README, G.templates, st.templates, "identity"),
    equals(SA, "stars", README, G.stars, st.stars, "identity"),
    equals(SA, "star additions before replacement (PR 7)", README, G.oldStar, st.oldStar, "identity"),
    equals(SA, "PR 7's published greedy total", README, G.newStar, st.pr7Star, "identity"),
    equals(SA, "best of the three rules per template, pruned, summed over the 20475 stars", README + ": 2,452,660", s.newStar, st.newStar),
    truth(SA, "every candidate gate joins two available disjoint terms, makes a new sum, and every request is made", README, s.allValid),
    equals(SA, "saving over PR 7: 2623060 - new", README + ": saves another 170,400 addition nodes", G.newStar - s.newStar, st.saved),
    equals(SA, "c = 11240978 - 3006276 + new star additions", README, c, st.c),
    equals(SA, "q unchanged", README, qq, st.q, "identity"),
    equals(SA, "R = c + q", README, c + qq, st.R),
    truth(OBS, "template winners (ties go to the first in the order large, large-reverse, published)", "derived", true, `${JSON.stringify(s.winners)}; with only large-first: ${s.largeOnly}; only large-reverse: ${s.largeRevOnly}`, "observation"),
  );

  const SB = "PR9-B F3 bit network with R = 11670540: eta_b, a_b = 761/10^11";
  const R = c + qq;
  const bn = primeFieldBitNetwork(H, R);
  const logm = cached("pr7 logm", () => logIntegerEnclosure(bn.m, 24));
  const expL0 = cached("pr7 exp", () => expLowerBound(st.L0, 80));
  const enc = savingEnclosure(bn.eta, logm);
  const v = bn.v;
  const Rmax = largestR(v - 6n * binom(H, 2) * BigInt(H - 2), 2n * bn.m, v, st.a, st.L0);
  out.push(
    equals(SB, "eta_b = (Wm - s)/(Wm)", README, bn.eta, st.eta),
    fromCheck(SB, { name: "log 21952 < 9997/1000 (atanh)", source: README, lhs: logm.upper, rel: "<", rhs: st.L0 }),
    truth(SB, "e^(9997/1000) > 21952 (Taylor, second route)", "derived", lt(q(bn.m), expL0)),
    fromCheck(SB, { name: "eta_b > a_b (9997/1000), a_b = 761/10^11", source: README, lhs: mul(st.a, st.L0), rel: "<", rhs: bn.eta }),
    truth(SB, "a_b < lower enclosure of -log(1 - eta_b)/log m (Mercator route)", README + ": exp(-x) > 1 - x supplies the strict saving", lt(st.a, enc.lower), `a* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    fromCheck(SB, { name: "1 - tau <= a_b", source: README, lhs: sub(ONE, p.tau), rel: "<=", rhs: st.a, kind: "condition" }),
    truth(OBS, "role budget for a_b = 761/10^11 with log m < 9997/1000", "derived", true, `R <= ${Rmax}; stated R leaves ${Rmax - R} roles (${toDecimal(q(Rmax - R, R), 6)} of R)`, "observation"),
  );

  const SC = "PR9-C assembly: PR 7's fast-Gaussian system with a_b = 761/10^11, kappa = 19/(5*10^9)";
  const x = layerExponents(p);
  const mg = fastMargins(p);
  const Gm = fastMinimumMargin(p);
  out.push(...fastParameterChecks(p).map((k) => fromCheck(SC, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SC, { name: `kappa < ${k}`, source: README + " (seven assembly margins)", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SC, "sigma < tau, so chi = tau", README, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SC, "C1 = 5 - 4 beta + zeta", README, sub(add(q(5n), p.zeta), mul(q(4n), p.beta)), p.C1),
    equals(SC, "G_* = g3", README, Gm, mg.g3),
    equals(SC, "G_* = 4754049/(125*10^13)", README, Gm, st.G),
    equals(SC, "G_* - kappa = 4049/(125*10^13)", README, sub(Gm, p.kappa), st.gap),
    truth(SC, "G_* = 3.8032392e-9 (decimal as stated)", README, toDecimal(Gm, 16) === st.Gdecimal, toDecimal(Gm, 18)),
    fromCheck(SC, { name: "kappa > 2^-28", source: README, lhs: twoPow(-28), rel: "<", rhs: p.kappa, kind: "condition" }),
    truth(SC, "380/373 is about 1.88% above PR 7 (rounds to 1.88)", README, (() => {
      const pct = mul(sub(div(p.kappa, q(373n, TEN(11))), ONE), q(100n));
      return !lt(pct, q(1875n, 1000n)) && lt(pct, q(1885n, 1000n));
    })(), toDecimal(mul(sub(div(p.kappa, q(373n, TEN(11))), ONE), q(100n)), 4) + "%"),
  );
  const SD = "PR9-D generalized guard (PR 7's complex network, unchanged)";
  const cc = computeComplex7();
  const cn = primeFieldComplexNetwork(H, BigInt(cc.additions + cc.injections));
  out.push(
    equals(SD, "R_c = 93838 (PR 7's complex circuit, rebuilt)", README, BigInt(cc.additions + cc.injections), STATED_PR7.Rc),
    ...compactGuardChecks(cn.W, cn.s, cn.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SD, k)),
    truth(OBS, "kappa / (a_b/2)", "derived", true, toDecimal(div(p.kappa, div(st.a, q(2n))), 6), "observation"),
    truth(OBS, "not checked: that the new templates keep PR 7's frame, bank-sharing and finite-alphabet interfaces (README's review question); the h = 8 controls", README, true, "", "observation"),
  );
  void compactGuardConstants;
  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { params: p, stars: { newStar: s.newStar, winners: s.winners, largeOnly: s.largeOnly, largeRevOnly: s.largeRevOnly }, c, q: qq, R, bit: bn, logm, enclosure: enc, margins: mg, G: Gm, Rmax, complex: cn } };
}
