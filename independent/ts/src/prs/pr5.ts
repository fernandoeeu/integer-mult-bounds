// PR 5 (eumemic): "Faster Gaussian resampling and a conditional integer-
// multiplication saving above 2^-30". Head d3d370c, base 6e56487; it contains
// PR 3 (dfe5b81) unchanged plus one commit. Sources: notes/fast-gaussian-note.tex,
// notes/fast-gaussian-resampling.tex, patches/fast-gaussian-30.patch.
//
// Top-down: both networks stay as in PR 3 (bit a = 296/10^11, compressed complex
// a_c = 14/10^9). Only the one-dimensional resampling maps change: a chirp
// identity turns every Gaussian line sum into correlations, and a potential
// argument bounds the powers of E = N - I, so the Neumann series needs at most
// about 30d terms with alpha = floor(sqrt(b/(8d))). The Gaussian cost row falls
// from power 3/4 + delta + 5eps/4 to 2eps + delta, which lifts the cap eps < 1/5
// to eps < 1/2. The assembly is re-solved: eps = 49999/100000, c = 9999/10000,
// beta = 19/25 (so C1 = 19601/10000), lambda = 1 - 29595/10^13,
// lambda' = 1 - 2959/10^12, kappa = 1479/10^12, G_* = g3 = 147947041/10^17.
// The larger beta is possible only because the compressed complex saving is large
// enough for the leaf (1 - beta) a_c > 1 - lambda'.

import { type Q, q, add, sub, mul, div, lt, le, eq, twoPow, ONE, show, toDecimal } from "../rational";
import { ground } from "../networks";
import { compactParameterChecks, layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { BIT_SAVING } from "../checks";
import { computeCircuit3, compressedNetwork, STATED_PR3 } from "./pr3";
import {
  fastParameterChecks,
  fastMargins,
  fastMinimumMargin,
  guardBetaThreshold,
  leafAndGuardCompatible,
  lemmaRows,
  exactPowerInstance,
  cutoff64d2,
  cutoff96d,
  DROPPED,
  ANALYTIC,
  FG_NOTE,
  FG_PATCH,
} from "./fastGaussian";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const NOTE = FG_NOTE;
const PATCH = FG_PATCH;

export const STATED_PR5 = {
  epsC1: q(980030399n, TEN(9)),
  C1: q(19601n, 10000n),
  G: q(147947041n, TEN(17)),
  gap: q(47041n, TEN(17)),
  alphaExp: q(50001n, 200000n),
  KExp: q(499940001n, TEN(9)),
  ellExp: q(50001n, 100000n),
  primeExp: q(1n, 50000n),
  ceilingFraction: q(999n, 1000n), // "above 99.9% of this bound"
  ratioOverPR3: q(251n, 100n), // "a factor 1479/590 ~ 2.51"
};

export function pr5Params(): CompactParams {
  const a = BIT_SAVING;
  const ac = q(14n, TEN(9));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(49999n, 100000n),
    c: q(9999n, 10000n),
    beta: q(19n, 25n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(19601n, 10000n),
    lambda: sub(ONE, q(29595n, TEN(13))),
    lambdaPrime: sub(ONE, q(2959n, TEN(12))),
    kappa: q(1479n, TEN(12)),
  };
}

/** Text errata: sentences of the patch whose numbers disagree with eq:fixed-parameters (observations, see REPORT). */
export function errataRows(section: string, p: CompactParams, patch: string, lineC1: number, lineD: number): Result[] {
  const staleC1 = q(49961n, 10000n);
  const staleEps = q(19999n, 100000n);
  return [
    truth(
      section,
      `ERRATUM ${patch} line ${lineC1}: "C_1=49961/10000, so eps C_1<1" holds at this eps`,
      `${patch} 08-assembly "Precision and exact recovery"`,
      lt(mul(p.epsilon, staleC1), ONE),
      `eps * 49961/10000 = ${show(mul(p.epsilon, staleC1))} (${toDecimal(mul(p.epsilon, staleC1), 6)}) > 1; with eq:fixed-parameters' C_1 = ${show(p.C1)}: ${toDecimal(mul(p.epsilon, p.C1), 6)} < 1; 49961/10000 is PR 3's C_1 (there eps C_1 = ${toDecimal(mul(staleEps, staleC1), 6)})`,
      "observation",
    ),
    truth(
      section,
      `ERRATUM ${patch} lines ${lineD}-${lineD + 1}: the example "d = floor(b^(19999/100000))" uses this eps`,
      `${patch} 08-assembly scalar setup`,
      eq(staleEps, p.epsilon),
      `the example's exponent is 19999/100000 (PR 3's eps); eps here is ${show(p.epsilon)}. Labelled "For example", so the procedure is unaffected`,
      "observation",
    ),
  ];
}

/** |x - y| < tol */
const within = (x: Q, y: Q, tol: Q) => {
  const d = sub(x, y);
  return lt(d.num < 0n ? q(-d.num, d.den) : d, tol);
};

export type PR5Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR5> };

export function pr5(opts: PR5Options = {}) {
  const st = { ...STATED_PR5, ...opts.stated };
  const p = opts.p ?? pr5Params();
  const out: Result[] = [];
  const g = ground(25);

  // ---- 5A: the networks are PR 3's, unchanged
  const SA = "PR5-A networks unchanged from PR 3 (compressed complex circuit rebuilt; bit network B2 of `bun run check`)";
  const c = computeCircuit3();
  const R = BigInt(c.additions + c.injections);
  const nw = compressedNetwork(25, R);
  out.push(
    equals(SA, "complex side roles R = c + q (rebuilt circuit)", "PR3 complex-circuit-construction.tex (unchanged in PR 5)", R, STATED_PR3.R),
    equals(SA, "W_c", "PR3 prop:compressed-complex-interface; certificate complex_counts", nw.W, STATED_PR3.W),
    equals(SA, "s_c", "PR3 prop:compressed-complex-interface", nw.s, STATED_PR3.s),
    equals(SA, "eta_c = 28/205789375", "PR3 prop:compressed-complex-interface", nw.eta, STATED_PR3.eta),
    fromCheck(SA, { name: "eta_c > a_c (966/100), a_c = 14/10^9 (log m_c < 966/100 checked in PR3-B)", source: "PR3 eq:compressed-complex-exponent", lhs: mul(p.ac, q(966n, 100n)), rel: "<", rhs: nw.eta, kind: "implied" }),
    fromCheck(SA, { name: "1 - sigma <= a_c = 14/10^9", source: NOTE + " Scope", lhs: sub(ONE, p.sigma), rel: "<=", rhs: q(14n, TEN(9)), kind: "condition" }),
    fromCheck(SA, { name: "1 - tau <= a_b = 296/10^11", source: NOTE + " Scope", lhs: sub(ONE, p.tau), rel: "<=", rhs: BIT_SAVING, kind: "condition" }),
  );

  // ---- 5B: the re-solved parameter system
  const SB = "PR5-B parameters, layer exponents and margins with the new Gaussian row";
  const x = layerExponents(p);
  const mg = fastMargins(p);
  const G = fastMinimumMargin(p);
  out.push(...fastParameterChecks(p).map((k) => fromCheck(SB, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SB, { name: `kappa < ${k}`, source: PATCH + " eq:margin-list (g5 = 1 - delta - 2 eps)", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  const thr = guardBetaThreshold(p);
  out.push(
    truth(SB, "sigma < tau, so chi = tau", NOTE, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SB, "C1 = 5 - 4 beta + zeta = 19601/10000", NOTE, sub(add(q(5n), p.zeta), mul(q(4n), p.beta)), st.C1),
    equals(SB, "eps C1 = 980030399/10^9", NOTE, mul(p.epsilon, p.C1), st.epsC1),
    fromCheck(SB, { name: "the guard forces beta > 3/4: (5 + zeta - 1/eps)/4 > 3/4", source: NOTE + ": eps C1 < 1 forces beta > 3/4", lhs: q(3n, 4n), rel: "<", rhs: thr }),
    fromCheck(SB, { name: "beta > (5 + zeta - 1/eps)/4 (the guard threshold)", source: NOTE + " (same inequality as eps C1 < 1)", lhs: thr, rel: "<", rhs: p.beta, kind: "implied" }),
    truth(SB, "with a_c = 418/10^12 no beta meets both the guard and (1-beta) a_c > kappa/eps", NOTE + ": with the original complex saving no beta satisfies both", !leafAndGuardCompatible(p, q(418n, TEN(12))), `needs a_c > ${toDecimal(div(div(p.kappa, p.epsilon), sub(ONE, thr)), 16)}`),
    truth(SB, "with a_c = 14/10^9 such a beta exists", NOTE, leafAndGuardCompatible(p, p.ac)),
    equals(SB, "G_* = g3", NOTE, G, mg.g3),
    equals(SB, "G_* = 147947041/10^17", NOTE, G, st.G),
    equals(SB, "G_* - kappa = 47041/10^17", NOTE, sub(G, p.kappa), st.gap),
    equals(SB, "alpha exponent (1 - eps)/2 = 50001/200000", PATCH, div(sub(ONE, p.epsilon), q(2n)), st.alphaExp),
    equals(SB, "K exponent eps c = 499940001/10^9", PATCH, mul(p.epsilon, p.c), st.KExp),
    equals(SB, "ell exponent 1 - eps = 50001/100000", PATCH, sub(ONE, p.epsilon), st.ellExp),
    equals(SB, "prime-interval ratio and b/d^2 grow as p^(1 - 2 eps) = p^(1/50000)", PATCH, sub(ONE, mul(q(2n), p.epsilon)), st.primeExp),
    fromCheck(SB, { name: "kappa > 2^-30", source: NOTE, lhs: twoPow(-30), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SB, { name: "kappa < 2^-29", source: NOTE, lhs: p.kappa, rel: "<", rhs: twoPow(-29), kind: "condition" }),
    truth(SB, "kappa / (59/10^11) = 1479/590 = 2.51 (to the stated digits)", NOTE + ": a factor 1479/590 ~ 2.51", within(div(p.kappa, q(59n, TEN(11))), st.ratioOverPR3, q(5n, 1000n)), toDecimal(div(p.kappa, q(59n, TEN(11))), 6)),
  );
  // the dropped conditions must indeed fail at this eps (otherwise the patch would not need to drop them)
  const OBS = "PR5-0 observations (not part of the claim)";
  const old = compactParameterChecks(p).filter((k) => DROPPED.includes(k.name));
  for (const k of old)
    out.push(truth(OBS, `PR 3's condition "${k.name}" at eps = 49999/100000 (dropped by the patch)`, "PR3 complex-circuit-31.patch", true, `${(k.rel === "<" ? lt(k.lhs, k.rhs) : le(k.lhs, k.rhs)) ? "holds" : "fails"} (lhs ${toDecimal(k.lhs, 6)}, rhs ${toDecimal(k.rhs, 6)})`, "observation"));

  // ---- 5C: generalized guard with beta = 19/25 (network unchanged)
  const SC = "PR5-C generalized guard with the compressed network at beta = 19/25";
  const gu = compactGuardConstants(nw.W, nw.s, nw.m, p.zeta);
  out.push(...compactGuardChecks(nw.W, nw.s, nw.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SC, k)));
  const depth = cached(`pr5 depth ${show(p.beta)} ${nw.s}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], nw.m, nw.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SC, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));

  // ---- 5D: the new Gaussian width
  const SD = "PR5-D Gaussian width alpha = floor(sqrt(b/(8d))), gamma = 2 d alpha^2 (patch 08-assembly)";
  out.push(
    truth(SD, "sqrt(b/(8d)) >= sqrt 12 > 2 + sqrt 2 (12 - 6 = 6 > 4 sqrt 2: 36 > 32), so alpha >= x - 1 >= x/sqrt 2: alpha^2 >= b/(16d) once b >= 96d", PATCH, 36 > 32, "", "constant"),
    fromCheck(SD, {
      name: "Neumann count: (6b+1) 16d/(4b) + 4d + 1 <= 30d at the worst case b = 96d, d = 1 (decreasing in b; slack 2d - 1 - 4d/b grows with d)",
      source: PATCH,
      lhs: add(add(div(mul(q(6n * 96n + 1n), q(16n)), q(4n * 96n)), q(4n)), ONE),
      rel: "<=",
      rhs: q(30n),
      kind: "constant",
    }),
    truth(SD, "2 eta/(1 - 2 eta) = 1/(2d - 1) <= 1/4 for d >= 3 (eta = 1/(4d); d = 3..50)", PATCH, Array.from({ length: 48 }, (_, k) => BigInt(k + 3)).every((d) => {
      const e = q(1n, 4n * d);
      return eq(div(mul(q(2n), e), sub(ONE, mul(q(2n), e))), q(1n, 2n * d - 1n)) && le(q(1n, 2n * d - 1n), q(1n, 4n));
    }), "", "identity"),
  );
  for (const k of [300000, 400000, 500000]) {
    const r = cached(`pr5 inst ${k} ${show(p.epsilon)}`, () => {
      try {
        return exactPowerInstance(k, p.epsilon);
      } catch (e) {
        return null;
      }
    });
    const ok = !!r && Object.values(r.facts).every(Boolean);
    out.push(truth(SD, `b = 2^${k}, d = floor(b^eps) exact: every stated bound (b >= 96d, b >= 64d^2, alpha >= 2, alpha^2 >= b/(16d), alpha^2 < p, gamma <= b/4, alpha^2 theta > 1, n <= 30d, n <= p)`, PATCH, ok, r ? `d = 2^${r.d.toString(2).length - 1}, alpha has ${r.alpha.toString(2).length} bits, n <= ${r.nMax}` : "k eps not an integer"));
  }
  out.push(
    truth(SD, "b >= 64 d^2 eventually: needs b^(1 - 2eps) >= 64, i.e. b >= 2^(6/(1-2eps))", PATCH + ": holds for large n because 2 eps < 1", true, `b >= 2^${toDecimal(cutoff64d2(p.epsilon), 4)}, i.e. log2 n beyond 2^300000 (astronomical, but fine for an O-bound)`, "observation"),
    truth(SD, "b >= 96 d eventually: b >= 2^(7/(1-eps)) suffices", PATCH, true, `b >= 2^${toDecimal(cutoff96d(p.epsilon), 4)}`, "observation"),
  );

  // ---- 5E: the finite parts of the new lemmas
  const SE = "PR5-E constants, identities and samples of the new resampling lemmas (independent of the witness)";
  out.push(...cached("pr5 lemma rows", () => lemmaRows(SE)));
  for (const a of ANALYTIC) out.push(truth("PR5-0 observations (not part of the claim)", `analytic, not checked: ${a}`, NOTE, true, "", "observation"));

  // ---- 5F: the next ceiling
  const SF = "PR5-F next ceiling kappa < a/2 (scoped to these networks and assembly inequalities)";
  const a2 = div(p.a, q(2n));
  out.push(
    fromCheck(SF, { name: "g2 = eps c a <= eps a", source: NOTE + ", The next ceiling", lhs: mg.g2, rel: "<=", rhs: mul(p.epsilon, p.a), kind: "implied" }),
    fromCheck(SF, { name: "g3 = eps (1 - lambda') < eps a (lambda' > tau)", source: NOTE, lhs: mg.g3, rel: "<", rhs: mul(p.epsilon, p.a), kind: "implied" }),
    equals(SF, "g4 = a (1 - eps)", NOTE, mg.g4, mul(p.a, sub(ONE, p.epsilon)), "identity"),
    fromCheck(SF, { name: "kappa < min{g2, g3, g4} <= a min{eps, 1-eps} <= a/2", source: NOTE, lhs: p.kappa, rel: "<", rhs: a2, kind: "implied" }),
    fromCheck(SF, { name: "a/2 = 148/10^11 < 2^-29", source: NOTE, lhs: a2, rel: "<", rhs: twoPow(-29), kind: "constant" }),
    fromCheck(SF, { name: "kappa > 99.9% of a/2", source: NOTE, lhs: mul(st.ceilingFraction, a2), rel: "<", rhs: p.kappa }),
  );

  // ---- 5T: text errata (observations)
  out.push(...errataRows("PR5-T stated constants in the patch text", p, "fast-gaussian-30.patch", 263, 215));

  const OBSALL = "PR5-0 observations (not part of the claim)";
  const ordered = [...out.filter((r) => r.section !== OBSALL), ...out.filter((r) => r.section === OBSALL)];
  return { results: ordered, values: { params: p, network: nw, circuit: c, guard: gu, margins: mg, G, exponents: x, threshold: thr } };
}
