// PR 8 (Rohan Arun): "Add conditional geometric complex-network candidate for
// review". Head 9454645, base 6e56487. Sources: research/geometric-complex/
// geometric-note.tex and README.md. Explicitly an unreviewed candidate; it does not
// patch the manuscript.
//
// Top-down: only the complex network changes; the bit network (a = 296/10^11) and the
// compact-control assembly of the head are kept.
//  (1) The complex motif keeps n = 25 ground points (v = 2300 triples) but adds one
//      label coordinate: label space F2^26, h = 26, m = 26^3 = 17576.
//  (2) The separate side wires become two dyadic-split sum circuits: D (disjoint
//      sums, 212737 additions, 2300 outputs) and E (pair-star partial sums, 36620
//      additions, 6900 outputs): R = 258557 roles per invocation.
//  (3) No bank sharing: W = 2N + 3v^2(R + n + 1), L = 3v^2 (n+1) h,
//      s = Wm - 2N + 2L, eta = 68/1714426753, certifying a_c = 4*10^-9.
//  (4) Guard with the new constants and a new per-invocation operation count
//      32 I (R + v + n + 1) + 4s + 4W + 4 < E_0.
//  (5) The compact assembly with eps = 1999/10000, c = 1, beta = 1/1000,
//      lambda = 1 - 2959/10^12, lambda' = 1 - 2958/10^12, kappa = 59/10^11;
//      G_* = g3 = 2956521/(5*10^15).

import { q, add, sub, mul, div, lt, le, eq, twoPow, ONE, ZERO, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { logIntegerEnclosure, expLowerBound } from "../log";
import { compactParameterChecks, compactMargins, compactMinimumMargin, layerExponents, type CompactParams } from "../compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "../compact/guard";
import { savingEnclosure } from "../compact/ceiling";
import { gaussianChecks, gaussianInstance } from "../gaussian";
import { BIT_SAVING } from "../checks";
import { dyadicCircuit, disjointRequests, intersectionTwoRequests, sideMapExact } from "./geometric";
import { buildPairedCircuit, PUBLISHED_CONVENTIONS } from "../circuit";
import { mergeGroups } from "../global";
import { fromCheck, equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const NOTE = "PR8 geometric-note.tex";
const README = "PR8 README.md";
const n = 25;

export const STATED_PR8 = {
  v: 2300n,
  m: 17576n,
  dAdditions: 212737,
  dOutputs: 2300,
  eAdditions: 36620,
  eOutputs: 6900,
  R: 258557n,
  baselineSideRoles: 3693800n,
  N: 12167000000n,
  W: 4128046210000n,
  L: 10728120000n,
  s: 72554537309200000n,
  eta: q(68n, 1714426753n),
  ac: q(4n, TEN(9)),
  leafGap: q(3996n, TEN(12)), // leaf exponent 1 - 3996/10^12
  epsOneC: q(3998n, 10000n), // eps(1 + c)
  epsC1: q(99872039n, TEN(8)),
  G: q(2956521n, 5n * TEN(15)),
  gapDecimal: q(13042n, TEN(16)), // G_* - kappa = 1.3042e-12
  ratio: "7.10843", // 590/83 ~ 7.10843
  ceilingFraction: q(996n, 1000n), // "over 99.6% of that ceiling"
  ceiling: q(592n, TEN(12)), // (296/10^11)/5 = 5.92e-10
};

export function pr8Params(): CompactParams {
  const a = BIT_SAVING;
  const ac = q(4n, TEN(9));
  return {
    a,
    ac,
    tau: sub(ONE, a),
    sigma: sub(ONE, ac),
    epsilon: q(1999n, 10000n),
    c: q(1n),
    beta: q(1n, 1000n),
    zeta: q(1n, 10000n),
    delta: q(1n, TEN(6)),
    C1: q(49961n, 10000n),
    lambda: sub(ONE, q(2959n, TEN(12))),
    lambdaPrime: sub(ONE, q(2958n, TEN(12))),
    kappa: q(59n, TEN(11)),
  };
}

/** PR 8's network: n ground points, label dimension h = n + 1, no bank sharing. */
export function geometricNetwork(nn: number, R: bigint) {
  const v = binom(nn, 3);
  const h = BigInt(nn + 1);
  const m = h ** 3n;
  const N = v ** 3n;
  const I = 3n * v * v;
  const W = 2n * N + I * (R + BigInt(nn) + 1n);
  const L = I * (BigInt(nn) + 1n) * h;
  const s = W * m - 2n * N + 2n * L;
  return { v, h, m, N, I, W, L, s, D: W * m - s, eta: q(W * m - s, W * m) };
}

export function computeCircuits8() {
  return cached("pr8 circuits", () => {
    const D = dyadicCircuit(2300, disjointRequests(n));
    const Ereq = intersectionTwoRequests(n);
    const E = dyadicCircuit(2300, Ereq.requests);
    let shared = 0;
    for (const k of D.nodes.keys()) if (E.nodes.has(k)) shared++;
    const map = sideMapExact(n);
    const strip = (c: typeof D) => ({ additions: c.additions, outputs: c.outputs, outputsExact: c.outputsExact, allDisjoint: c.allDisjoint, maxDepth: c.maxDepth });
    return { D: strip(D), E: strip(E), shared, map };
  });
}

export type PR8Options = { p?: CompactParams; stated?: Partial<typeof STATED_PR8>; observation?: boolean };

export function pr8(opts: PR8Options = {}) {
  const st = { ...STATED_PR8, ...opts.stated };
  const p = opts.p ?? pr8Params();
  const out: Result[] = [];
  const OBS = "PR8-0 observations (not part of the claim)";

  // ---- 8A: the two circuits
  const SA = "PR8-A dyadic-split side circuits D and E at n = 25 (rebuilt from the note; fully determined by it)";
  const c = computeCircuits8();
  const R = BigInt(c.D.additions + c.D.outputs + c.E.additions + c.E.outputs);
  out.push(
    equals(SA, "D additions", NOTE + " table", c.D.additions, st.dAdditions),
    equals(SA, "D partial outputs", NOTE + " table", c.D.outputs, st.dOutputs),
    equals(SA, "E additions", NOTE + " table", c.E.additions, st.eAdditions),
    equals(SA, "E partial outputs = C(25,2) * 23", NOTE + " table", c.E.outputs, st.eOutputs),
    truth(SA, "every output node has exactly its requested support (D: disjoint from S; E: pair-star of P minus S)", NOTE, c.D.outputsExact && c.E.outputsExact),
    truth(SA, "every addition joins its two disjoint dyadic halves", NOTE, c.D.allDisjoint && c.E.allDisjoint),
    truth(SA, "side map (1/2)D - (1/2)E exact: +1/2 on disjoint, -1/2 on intersection two, 0 otherwise, each once", NOTE + ": (1/2)D - (1/2)E + R_0 G = I", c.map.exact),
    equals(SA, "R = roles of D plus roles of E (c + q each)", NOTE + ": R = 258557", R, st.R),
    equals(SA, "baseline separate side wires v (C(22,3) + 66)", NOTE, 2300n * (binom(22, 3) + 66n), st.baselineSideRoles, "identity"),
    equals(SA, "nonzero side coefficients = baseline side wires", NOTE, BigInt(c.map.nonzero), st.baselineSideRoles, "identity"),
    truth(SA, "central coefficient (k-1)/2 makes (1/2)[k=0] - (1/2)[k=2] + (k-1)/2 = [k=3] for k = 0..3", NOTE, [0, 1, 2, 3].every((k) => eq(add(sub(q(k === 0 ? 1n : 0n, 2n), q(k === 2 ? 1n : 0n, 2n)), q(BigInt(k - 1), 2n)), q(k === 3 ? 1n : 0n))), "", "constant"),
    truth(OBS, "D and E share supports (the note interns within each circuit)", "derived", true, `${c.shared} supports occur in both; joint interning would save that many additions`, "observation"),
  );

  // ---- 8B: the network
  const SB = "PR8-B network counts, eta, a_c = 4*10^-9 (h = 26 label coordinates, m = 26^3)";
  const nw = geometricNetwork(n, R);
  const logm = cached("pr8 logm", () => logIntegerEnclosure(nw.m, 24));
  const L0 = q(9775n, 1000n); // a rational upper bound chosen here (the note gives none)
  const expL0 = cached("pr8 exp", () => expLowerBound(L0, 80));
  const enc = savingEnclosure(nw.eta, logm);
  const q8 = BigInt(c.D.outputs + c.E.outputs);
  out.push(
    equals(SB, "v = C(25,3)", NOTE, nw.v, st.v),
    equals(SB, "m = 26^3", NOTE, nw.m, st.m),
    equals(SB, "N = v^3", NOTE, nw.N, st.N),
    equals(SB, "W = 2N + 3v^2 (R + n + 1)", NOTE, nw.W, st.W),
    equals(SB, "L_dec = 3v^2 (n+1) h", NOTE, nw.L, st.L),
    equals(SB, "s = W m - 2N + 2 L_dec", NOTE, nw.s, st.s),
    truth(SB, "L_dec < N (positive deficit)", NOTE, nw.L < nw.N),
    equals(SB, "eta = (W m - s)/(W m)", NOTE, nw.eta, st.eta),
    truth(SB, "log 17576 < 9775/1000 (atanh) and e^(9775/1000) > 17576 (Taylor); bound chosen here", "derived", lt(logm.upper, L0) && lt(q(nw.m), expL0), `log m in [${toDecimal(logm.lower, 8)}, ${toDecimal(logm.upper, 8)}]`),
    fromCheck(SB, { name: "eta > a_c log m, a_c = 4*10^-9 (upper enclosure of log m)", source: NOTE + ": exact rational logarithm bounds certify eta > (4e-9) log m", lhs: mul(st.ac, logm.upper), rel: "<", rhs: nw.eta }),
    truth(SB, "a_c < lower enclosure of the actual saving -log(1 - eta)/log m (Mercator route)", NOTE + ": s/W < m^(1-4e-9)", lt(st.ac, enc.lower), `a_c* in [${toDecimal(enc.lower, 14)}, ${toDecimal(enc.upper, 14)}]`),
    equals(SB, "tensor accounting: 3 stages of (R+h)m + 2va(h-1) + 2h^2 (a = h^(j-1)), times v^2, = W m - 2N + 2L_dec", NOTE + ", Audit section", nw.v * nw.v * ([1n, nw.h, nw.h * nw.h].reduce((acc, a) => acc + (R + nw.h) * nw.m + 2n * nw.v * a * (nw.h - 1n) + 2n * nw.h * nw.h, 0n)), nw.W * nw.m - 2n * nw.N + 2n * nw.L, "identity"),
    fromCheck(SB, { name: "1 - sigma <= a_c", source: NOTE, lhs: sub(ONE, p.sigma), rel: "<=", rhs: st.ac, kind: "condition" }),
    fromCheck(SB, { name: "1 - tau <= a_b = 296/10^11 (bit network unchanged; B2 of `bun run check`)", source: NOTE, lhs: sub(ONE, p.tau), rel: "<=", rhs: BIT_SAVING, kind: "condition" }),
    truth(OBS, "largest a_c on the 10^-11 grid with log m below the atanh upper bound", "derived", true, (() => {
      let k = 400n;
      while (lt(mul(q(k + 1n, TEN(11)), logm.upper), nw.eta)) k++;
      return `${k}/10^11`;
    })(), "observation"),
  );

  // ---- 8C: the guard with the new constants
  const SC = "PR8-C generalized guard with the new complex network (m = 17576, beta = 1/1000)";
  const gu = compactGuardConstants(nw.W, nw.s, nw.m, p.zeta);
  out.push(...compactGuardChecks(nw.W, nw.s, nw.m, p.beta, p.zeta, p.C1).map((k) => fromCheck(SC, k)));
  const opsBound = 32n * (R + nw.v + BigInt(n) + 1n);
  out.push(
    fromCheck(SC, { name: "operation count 8R + 4v + 4q + 18v (q = 4v) <= 32(R + v + n + 1)", source: NOTE + ", Coefficient guard", lhs: q(8n * R + 4n * nw.v + 4n * q8 + 18n * nw.v), rel: "<=", rhs: q(opsBound) }),
    equals(SC, "q = D outputs + E outputs = 4v", NOTE, q8, 4n * nw.v, "identity"),
    fromCheck(SC, { name: "32 I (R + v + n + 1) + 4s + 4W + 4 < E_0", source: NOTE + ", Coefficient guard", lhs: q(nw.I * opsBound + 4n * nw.s + 4n * nw.W + 4n), rel: "<", rhs: q(gu.E) }),
  );
  const depth = cached(`pr8 depth ${show(p.beta)} ${nw.s}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], nw.m, nw.s, gu.E, gu.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  out.push(truth(SC, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta)", "compact-control-guard.tex", depth.ok, depth.detail));

  // ---- 8D: parameters and margins (compact system of the head)
  const SD = "PR8-D compact-control parameters with c = 1, layer exponents, margins";
  const x = layerExponents(p);
  const mg = compactMargins(p);
  const G = compactMinimumMargin(p);
  out.push(...compactParameterChecks(p).map((k) => fromCheck(SD, k)));
  for (const [k, gk] of Object.entries(mg)) out.push(fromCheck(SD, { name: `kappa < ${k}`, source: NOTE + ": seven retained assembly margins", lhs: p.kappa, rel: "<", rhs: gk, kind: "condition" }));
  out.push(
    truth(SD, "sigma < tau, so chi = tau", NOTE, lt(p.sigma, p.tau) && eq(x.chi, p.tau)),
    equals(SD, "leaf exponent sigma + beta(1 - sigma) = 1 - 3996/10^12", NOTE, x.leaf, sub(ONE, st.leafGap)),
    equals(SD, "reservation exponent max{1 - c, 0} = 0", NOTE, x.reserve, ZERO),
    equals(SD, "eps(1 + c) = 3998/10000", NOTE, mul(p.epsilon, add(ONE, p.c)), st.epsOneC),
    equals(SD, "eps C1 = 99872039/10^8", NOTE, mul(p.epsilon, p.C1), st.epsC1),
    equals(SD, "C1 = 5 - 4 beta + zeta = 49961/10000", NOTE, sub(add(q(5n), p.zeta), mul(q(4n), p.beta)), p.C1, "identity"),
    equals(SD, "G_* = g3", NOTE, G, mg.g3),
    equals(SD, "G_* = 2956521/(5*10^15)", NOTE, G, st.G),
    equals(SD, "G_* - kappa = 1.3042*10^-12", NOTE, sub(G, p.kappa), st.gapDecimal),
    truth(SD, "G_* = 5.913042*10^-10 (decimal as stated)", NOTE, toDecimal(G, 16) === "0.0000000005913042", toDecimal(G, 18)),
    fromCheck(SD, { name: "kappa > 2^-31", source: NOTE + " abstract", lhs: twoPow(-31), rel: "<", rhs: p.kappa, kind: "condition" }),
    fromCheck(SD, { name: "kappa < 2^-30", source: "derived (the dyadic bracket)", lhs: p.kappa, rel: "<", rhs: twoPow(-30), kind: "condition" }),
    truth(SD, "kappa / (83/10^12) = 590/83 = 7.10843 (to the stated digits)", NOTE, toDecimal(div(p.kappa, q(83n, TEN(12))), 5) === st.ratio, toDecimal(div(p.kappa, q(83n, TEN(12))), 8)),
    truth(SD, "about 7.11 times the head's saving", README, toDecimal(div(p.kappa, q(83n, TEN(12))), 2) === "7.10" || toDecimal(div(p.kappa, q(83n, TEN(12))), 2) === "7.11", "590/83 = 7.108..., which rounds to 7.11"),
  );

  // ---- 8E: Gaussian width at eps = 1999/10000 (the head's construction)
  const SE = "PR8-E Gaussian width (eps = 1999/10000, the head's construction)";
  const gExp = add(q(1n, 2n), mul(q(3n, 2n), p.epsilon));
  const dup = (k: { name: string }) => k.name.startsWith("gamma exponent 1/2 + 3 eps/2");
  out.push(...gaussianChecks(p.epsilon, gExp, "compact-control-34.patch eq:gamma", 46n).map((k) => fromCheck(SE, dup(k) ? { ...k, kind: "implied" } : k)));
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`gauss ${e} ${show(p.epsilon)}`, () => gaussianInstance(e, p.epsilon));
    out.push(truth(SE, `b = 2^${e}: alpha, gamma meet every stated bound`, "compact-control-34.patch", r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }

  // ---- 8F: scoped ceiling and comparisons
  const SF = "PR8-F scoped ceiling kappa < a/5 and comparisons";
  const a5 = div(p.a, q(5n));
  out.push(
    equals(SF, "a/5 = 5.92*10^-10", NOTE, a5, st.ceiling),
    fromCheck(SF, { name: "kappa < g3 = eps(1 - lambda') < eps a < a/5", source: NOTE, lhs: mg.g3, rel: "<", rhs: a5, kind: "implied" }),
    fromCheck(SF, { name: "kappa > 99.6% of a/5", source: NOTE, lhs: mul(st.ceilingFraction, a5), rel: "<", rhs: p.kappa }),
    truth(OBS, "would it improve the repository head (83/10^12) if valid?", "derived", true, `yes: ${toDecimal(div(p.kappa, q(83n, TEN(12))), 4)} times; it equals PR 3's claimed kappa (59/10^11) and is below PRs 5, 6, 7 (1479/10^12, 1624/10^12, 373/10^11), which rest on other constructions`, "observation"),
    truth(OBS, "c = 1 lies outside the range used by every earlier witness (c < 1) but no written condition excludes it: the layout uses max{1 - c, 0}", "compact-control-layout.tex, Unrolling; compact-control-34.patch prop:simultaneous-layer", true, "", "observation"),
  );

  if (opts.observation) {
    const sc = bitScreen();
    out.push(
      truth(OBS, "bit screen (README): x, y in {30..70} by twos, circuits rebuilt; the (50, 50, 50) network is the unique winner", README + "; bit_screen.py", sc.winner.x === 50 && sc.winner.y === 50 && sc.unique, `${sc.pairs} pairs, ${sc.cases} with positive deficit; winner (${sc.winner.x}, ${sc.winner.y}, ${sc.winner.x}), saving in [${toDecimal(sc.winner.lower, 14)}, ${toDecimal(sc.winner.upper, 14)}]`, "observation"),
    );
  }

  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { params: p, circuits: c, R, network: nw, logm, enclosure: enc, guard: gu, margins: mg, G, exponents: x, q: q8, opsBound } };
}

/** The bit screen's formulas (not part of the witness): outer size x, middle size y, side roles R_x, R_y. */
export function bitScreenCase(x: number, y: number, Rx: bigint, Ry: bigint) {
  const v = binom(x, 3);
  const u = binom(y, 3);
  const X = BigInt(x);
  const Y = BigInt(y);
  const N = v * v * u;
  const m = X * X * Y;
  const L = 2n * v * u * X * X + v * v * Y * Y;
  const D = N - 2n * L;
  const W = 2n * N + v * u * (Rx + X) + v * v * (Ry + Y);
  return { N, m, L, D, W, eta: D > 0n ? q(D, W * m) : null };
}

/**
 * The bit screen (README, bit_screen.py; not part of the witness): for outer and middle sizes
 * x, y in {30, 32, ..., 70}, rebuild the paired circuit (the repository's published conventions,
 * src/circuit.ts and src/global.ts) to get R_x = c + q, then enclose the saving of every case with
 * a positive deficit. About a minute.
 */
export function bitScreen(sizes: number[] = Array.from({ length: 21 }, (_, i) => 30 + 2 * i)) {
  return cached(`pr8 screen ${sizes.join(",")}`, () => {
    const counts = new Map<number, { additions: number; outputs: number; R: bigint }>();
    for (const x of sizes) {
      const G = mergeGroups(buildPairedCircuit(x - 1, PUBLISHED_CONVENTIONS), x);
      counts.set(x, { additions: G.left.length, outputs: G.outputs.length, R: BigInt(G.left.length + G.outputs.length) });
    }
    const logs = new Map<bigint, ReturnType<typeof logIntegerEnclosure>>();
    const cases: { x: number; y: number; lower: Q; upper: Q; eta: Q; W: bigint; N: bigint; L: bigint; m: bigint }[] = [];
    for (const x of sizes)
      for (const y of sizes) {
        const r = bitScreenCase(x, y, counts.get(x)!.R, counts.get(y)!.R);
        if (!r.eta) continue;
        if (!logs.has(r.m)) logs.set(r.m, logIntegerEnclosure(r.m, 24));
        const e = savingEnclosure(r.eta, logs.get(r.m)!);
        cases.push({ x, y, lower: e.lower, upper: e.upper, eta: r.eta, W: r.W, N: r.N, L: r.L, m: r.m });
      }
    let best = cases[0]!;
    for (const c of cases) if (lt(best.lower, c.lower)) best = c;
    const unique = cases.every((c) => c === best || lt(c.upper, best.lower));
    return { counts, cases: cases.length, pairs: sizes.length ** 2, winner: best, unique };
  });
}
