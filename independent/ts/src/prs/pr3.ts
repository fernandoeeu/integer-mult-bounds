// PR 3 (eumemic): "A compressed complex network and a conditional integer-
// multiplication saving above 2^-31". Sources: notes/complex-circuit-note.tex,
// notes/complex-circuit-construction.tex, patches/complex-circuit-31.patch at prs/3
// (base 6e56487).
//
// Top-down: the complex motif keeps h = 25, its central wires and frames; only its
// side circuit changes: 3693800 side wires per invocation become R = c + q =
// 80595 + 27600 = 108195 shared roles. The interface formulas
// W = 2N + 3v^2(R + h + 1), L = 3v^2 h(h+1), s = Wm - 2N + 2L give
// eta_c = 28/205789375 and certify a_c = 14/10^9 (was 418/10^12). Then sigma < tau,
// the bit network binds, and the compact-control parameter system is re-solved
// with eps = 19999/100000, c = 999/1000, lambda = 1 - 2958/10^12,
// lambda' = 1 - 2956/10^12, kappa = 59/10^11 (G_* = g3).

import { q, add, sub, mul, div, lt, eq, twoPow, ONE, show, toDecimal } from "../rational";
import { ground } from "../networks";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { compactParameterChecks, compactMargins, compactMinimumMargin, layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { gaussianChecks, gaussianInstance } from "../gaussian";
import { BIT_SAVING } from "../checks";
import { buildComplexCircuit, verifyComplexCircuit } from "./complexCircuit";
import { fromCheck, equals, truth, cached, type Result } from "./rows";
import { binom } from "../intmath";

const TEN = (k: number) => 10n ** BigInt(k);
const NOTE = "PR3 complex-circuit-note.tex";
const CON = "PR3 complex-circuit-construction.tex";
const PATCH = "PR3 complex-circuit-31.patch";
const H = 25;

export const STATED_PR3 = {
  additions: 80595,
  disjointAdditions: 68595,
  starAdditions: 12000,
  injections: 27600,
  piecesPerTarget: 12,
  sideWires: 3693800n,
  R: 108195n,
  labels: 82895, // "all 82895 labels" = inputs + additions
  inclusions: 188790, // "188790 inclusions" = 2 c + q
  W: 1741801270000n,
  L: 10315500000n,
  s: 27215641140750000n,
  eta: q(28n, 205789375n),
  gates: 5408242080000n,
  L0c: q(966n, 100n),
  ac: q(14n, TEN(9)),
  G: q(14779261n, 25n * TEN(15)),
  gap: q(29261n, 25n * TEN(15)),
  epsC1: q(999170039n, TEN(9)),
  alphaExp: q(119999n, 400000n),
  gammaExp: q(159997n, 200000n),
  primeExp: q(30001n, 50000n),
  KExp: q(19979001n, TEN(8)),
  ellExp: q(80001n, 100000n),
  ceilingFraction: q(996n, 1000n), // "above 99.6% of this bound"
};

export function pr3Params(): CompactParams {
  const a = BIT_SAVING;
  const ac = q(14n, TEN(9));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(19999n, 100000n),
    c: q(999n, 1000n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(49961n, 10000n),
    lambda: sub(ONE, q(2958n, TEN(12))),
    lambdaPrime: sub(ONE, q(2956n, TEN(12))),
    kappa: q(59n, TEN(11)),
  };
}

/** The compressed complex network's counts from the interface formulas of prop:compressed-complex-interface. */
export function compressedNetwork(h: number, R: bigint) {
  const { v, N, m } = ground(h);
  const H_ = BigInt(h);
  const W = 2n * N + 3n * v * v * (R + H_ + 1n);
  const L = 3n * v * v * H_ * (H_ + 1n);
  const s = W * m - 2n * N + 2n * L;
  return { v, N, m, W, L, s, deficit: W * m - s, eta: q(W * m - s, W * m) };
}

export function computeCircuit3() {
  return cached("pr3 circuit", () => verifyComplexCircuit(buildComplexCircuit(H, "leftFold")));
}

export type PR3Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR3>; circuit?: ReturnType<typeof computeCircuit3> };

export function pr3(opts: PR3Options = {}) {
  const st = { ...STATED_PR3, ...opts.stated };
  const p = opts.p ?? pr3Params();
  const out: Result[] = [];
  const c = opts.circuit ?? computeCircuit3();
  const g = ground(H);

  // ---- 3A: the compressed side circuit (rebuilt)
  const SA = "PR3-A compressed side circuit at h = 25 (rebuilt from the construction note)";
  const R = BigInt(c.additions + c.injections);
  out.push(
    equals(SA, "additions c (after removing nodes that feed no piece)", CON, c.additions, st.additions),
    equals(SA, "disjoint-sum additions", CON, c.disjointAdditions, st.disjointAdditions),
    equals(SA, "pair-star additions", CON, c.starAdditions, st.starAdditions),
    equals(SA, "injected pieces q", CON, c.injections, st.injections),
    truth(SA, "every target receives exactly twelve pieces", CON, c.piecesPerTarget.min === st.piecesPerTarget && c.piecesPerTarget.max === st.piecesPerTarget, `${c.piecesPerTarget.min}..${c.piecesPerTarget.max}`),
    equals(SA, "disjoint pieces split by the injection rule (the note: never at h = 25)", CON, c.splitDisjoint, 0),
    equals(SA, "pair-star pieces split by the rule (pi_22 for i = 23 and sigma_2 for i = 1, per pair): 2 C(25,2)", CON, c.splitStar, 2 * Number(binom(25, 2))),
    equals(SA, "empty disjoint pieces", CON + ": the six pieces partition the disjoint triples", c.emptyPieces, 0),
    truth(SA, "side map exact: +1/2 on every disjoint triple, -1/2 on every intersection-two triple, 0 elsewhere, each once", CON, c.sideMapExact),
    equals(SA, "nonzero side coefficients = v z_c", CON, BigInt(c.nonzeroCoefficients), st.sideWires),
    equals(SA, "v z_c = v (C(22,3) + 3*22)", CON + ": vz_c = 3693800 side wires", g.v * (binom(22, 3) + 66n), st.sideWires, "identity"),
    truth(SA, "every addition joins disjoint supports (supports recomputed from the kept additions)", CON, c.allAdditionsDisjoint),
    truth(SA, "every piece's triples meet the target in 0 or 2 points (implied by exactness)", CON, c.piecesMeetTargetEvenly, "", "implied"),
    equals(SA, "inputs used", CON, c.inputsUsed, 2300, "identity"),
    equals(SA, "R = c + q roles (the note's identity applied to the recomputed counts)", CON + ", The transparent schedule", R, st.R, "identity"),
    equals(SA, "labels = inputs + additions", NOTE + ": checks all 82895 labels", c.inputsUsed + c.additions, st.labels, "identity"),
    equals(SA, "inclusions = 2c + q", NOTE + ": 188790 inclusions", 2 * c.additions + c.injections, st.inclusions, "identity"),
  );

  // ---- 3B: network counts and the complex saving
  const SB = "PR3-B compressed complex network: counts, eta_c, a_c = 14/10^9";
  const nw = compressedNetwork(H, R);
  const logm = cached("pr3 logm", () => logIntegerEnclosure(g.m, 24));
  const expL0 = cached(`pr3 exp ${show(st.L0c)}`, () => expLowerBound(st.L0c, 60));
  const enc = savingEnclosure(nw.eta, logm);
  const gatesPerInvocation = 4n * (BigInt(c.inputsUsed) + BigInt(c.additions)) + 2n * g.v + 2n * g.v + 4n;
  const gates = 3n * g.v * g.v * gatesPerInvocation;
  out.push(
    equals(SB, "W_c = 2N + 3v^2(R + h + 1)", CON + " prop:compressed-complex-interface", nw.W, st.W),
    equals(SB, "L_c = 3 v^2 h (h+1)", CON, nw.L, st.L),
    equals(SB, "s_c = W_c m - 2N + 2L_c", CON, nw.s, st.s),
    equals(SB, "eta_c = (W_c m - s_c)/(W_c m)", CON, nw.eta, st.eta),
    truth(SB, "L_c < N (positive deficit)", CON, nw.L < nw.N),
    fromCheck(SB, { name: "log m_c < 966/100 (atanh, 24 terms)", source: CON + " eq:compressed-complex-exponent", lhs: logm.upper, rel: "<", rhs: st.L0c }),
    truth(SB, "e^(966/100) > m_c (Taylor partial sum, second route)", CON, lt(q(g.m), expL0)),
    fromCheck(SB, { name: "eta_c > a_c (966/100), a_c = 14/10^9", source: CON + " eq:compressed-complex-exponent", lhs: mul(st.ac, st.L0c), rel: "<", rhs: nw.eta }),
    truth(SB, "a_c < lower enclosure of the actual saving -log(1 - eta_c)/log m_c (Mercator route)", CON, lt(st.ac, enc.lower), `a* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    equals(SB, "gates = 3v^2 (4(v + c) + 2v + 2v + 4)", CON + ": 4*82895 mixer, 2v copy, 2v injection, four central gates per invocation", gates, st.gates),
    fromCheck(SB, { name: "gates <= 12 W_c", source: CON, lhs: q(gates), rel: "<=", rhs: q(12n * nw.W) }),
    truth(SB, "a_c / (418/10^12) = 33.49 (to the stated digits)", CON + ": 33.49 times the previous complex saving", toDecimal(div(st.ac, q(418n, TEN(12))), 2) === "33.49", toDecimal(div(st.ac, q(418n, TEN(12))), 6)),
    truth(SB, "a_c / a = 4.7 (to the stated digit)", NOTE + ": a_c exceeds a by a factor 4.7", toDecimal(div(st.ac, BIT_SAVING), 1) === "4.7", toDecimal(div(st.ac, BIT_SAVING), 6)),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: NOTE, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "1 - tau <= a_b = 296/10^11 (bit network unchanged; B2 of `bun run check`)", source: NOTE, lhs: sub(ONE, p.tau), rel: "<=", rhs: BIT_SAVING, kind: "condition" }),
  );

  // ---- 3C: generalized guard with the new network
  const SC = "PR3-C generalized guard with the compressed network (beta = 1/1000, zeta = 1/10000)";
  const gu = compactGuardConstants(nw.W, nw.s, nw.m, p.zeta);
  out.push(...compactGuardChecks(nw.W, nw.s, nw.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SC, k)));
  const depth = cached(`pr3 depth ${show(p.beta)}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], nw.m, nw.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SC, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));

  // ---- 3D: parameters, exponents, margins
  const SD = "PR3-D compact-control parameters, layer exponents, margins";
  const x = layerExponents(p);
  const mg = compactMargins(p);
  const G = compactMinimumMargin(p);
  out.push(...compactParameterChecks(p).map((k) => fromCheck(SD, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SD, { name: `kappa < ${k}`, source: NOTE + ": G_* - kappa > 0", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SD, "sigma < tau, so chi = tau", NOTE, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SD, "eps C1 = 999170039/10^9", NOTE, mul(p.epsilon, p.C1), st.epsC1),
    equals(SD, "C1 = 5 - 4 beta + zeta = 49961/10000", NOTE, sub(q(5n), sub(mul(q(4n), p.beta), p.zeta)), p.C1, "identity"),
    equals(SD, "alpha exponent 1/4 + eps/4 = 119999/400000", NOTE, add(q(1n, 4n), mul(q(1n, 4n), p.epsilon)), st.alphaExp),
    equals(SD, "gamma exponent 1/2 + 3 eps/2 = 159997/200000", NOTE, add(q(1n, 2n), mul(q(3n, 2n), p.epsilon)), st.gammaExp),
    equals(SD, "prime-interval exponent 1 - 2 eps = 30001/50000", NOTE, sub(ONE, mul(q(2n), p.epsilon)), st.primeExp),
    equals(SD, "K exponent eps c = 19979001/10^8", PATCH, mul(p.epsilon, p.c), st.KExp),
    equals(SD, "ell exponent 1 - eps = 80001/100000", PATCH, sub(ONE, p.epsilon), st.ellExp),
    equals(SD, "G_* = g3", NOTE, G, mg.g3),
    equals(SD, "G_* = 14779261/(25*10^15)", NOTE, G, st.G),
    equals(SD, "G_* - kappa = 29261/(25*10^15)", NOTE, sub(G, p.kappa), st.gap),
    fromCheck(SD, { name: "with c = 1/5, g2 < g3 (the note: c = 1/5 would make g2 binding)", source: NOTE, lhs: compactMargins({ ...p, c: q(1n, 5n) }).g2, rel: "<", rhs: mg.g3 }),
    fromCheck(SD, { name: "kappa > 2^-31", source: NOTE, lhs: twoPow(-31), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < 2^-30", source: NOTE, lhs: p.kappa, rel: "<", rhs: twoPow(-30), kind: "condition" }),
    equals(SD, "kappa / (83/10^12) = 590/83", NOTE, div(p.kappa, q(83n, TEN(12))), q(590n, 83n)),
  );

  // ---- 3E: Gaussian width at eps = 19999/100000
  const SE = "PR3-E Gaussian width (eps = 19999/100000)";
  const dup = (k: { name: string }) => k.name.startsWith("gamma exponent 1/2 + 3 eps/2");
  out.push(...gaussianChecks(p.epsilon, st.gammaExp, PATCH + " eq:gamma", 46n).map((k) => fromCheck(SE, dup(k) ? { ...k, kind: "implied" } : k)));
  out.push(
    fromCheck(SE, { name: "eps < 1/5 (the note's cutoff argument)", source: NOTE, lhs: p.epsilon, rel: "<", rhs: q(1n, 5n), kind: "implied" }),
    fromCheck(SE, { name: "184 < 2^8", source: NOTE, lhs: q(184n), rel: "<", rhs: q(256n), kind: "constant" }),
  );
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`gauss ${e} ${show(p.epsilon)}`, () => gaussianInstance(e, p.epsilon));
    out.push(truth(SE, `b = 2^${e}: alpha, gamma meet every stated bound`, PATCH, r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }

  // ---- 3F: the next ceiling (scoped)
  const SF = "PR3-F next ceiling kappa < a/5 (scoped to this bit network and these assembly inequalities)";
  const a5 = div(p.a, q(5n));
  out.push(
    fromCheck(SF, { name: "chain on the witness: kappa < g3 = eps(1 - lambda') < eps a < a/5", source: NOTE + ", The next ceiling", lhs: mg.g3, rel: "<", rhs: a5, kind: "implied" }),
    fromCheck(SF, { name: "a/5 = 296/(5*10^11) < 2^-30", source: NOTE, lhs: a5, rel: "<", rhs: twoPow(-30), kind: "constant" }),
    fromCheck(SF, { name: "kappa > 99.6% of a/5", source: NOTE, lhs: mul(st.ceilingFraction, a5), rel: "<", rhs: p.kappa }),
  );

  return { results: out, values: { circuit: c, network: nw, logm, enclosure: enc, guard: gu, params: p, exponents: x, margins: mg, G, gates, gatesPerInvocation } };
}
