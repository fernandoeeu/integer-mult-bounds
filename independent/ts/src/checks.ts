// Runs the checks and returns flat lists of results plus the recomputed values.
// Nothing here prints; main.ts prints, compare.ts compares with the certificates.
//
// Three groups:
//   bitNetwork()   the paired-block bit network at h = 50 and its exponent
//                  tau = 1 - 296/10^11. Used by BOTH witnesses: the preserved
//                  2^-59 witness and the current compact-control witness.
//   paired59(...)  the rest of the preserved 2^-59 witness (complex network at
//                  h = 50, parameters, guard, Gaussian width, room left).
//   compact(...)   the current compact-control witness kappa = 83/10^12
//                  (complex network at h = 25, parameters, generalized guard,
//                  Gaussian width, scoped ceiling, layout and repair arithmetic).
//
// Every result has a kind:
//   "check"       involves a value recomputed here (circuit facts, counts, rank deficits,
//                 enclosures, guard constants, displayed exponents and margins, sampled
//                 instances) and has an admissible input that makes it fail;
//   "condition"   a comparison the note states between its own input parameters; nothing is
//                 recomputed; it fails when a parameter moves past the stated limit; counted
//                 separately from "check", one per stated comparison (they overlap logically);
//   "constant"    compares numbers written inside a note's argument, independent of the witness
//                 parameters (fails only if the note's constant is wrong); counted separately;
//   "sample"      finite instances of a general claim of a note that does not depend on the
//                 witness (the repair bound for p = 2..4096, the four-update identity on a box);
//                 fails only if the claim, as written, is false; counted separately;
//   "identity"    holds for every admissible input, or by construction of the code; printed
//                 with its value for reference and not counted;
//   "implied"     follows from rows that are counted elsewhere; printed, not counted;
//   "observation" not part of either witness (the conventions observation of the README);
//                 printed, not counted, and does not enter the verdict.
//
// Every number a note displays and a row compares against is collected in
// STATED_BIT, STATED_59 or STATED_COMPACT. The runners accept replacements for
// them (and for the witness parameters) so that tests can show each row rejects a
// misstated value; main.ts never replaces them except through --set (parameters).

import { type Q, q, show, eq, lt, le, twoPow, div, toDecimal, mul, sub, add, ONE } from "./rational";
import { ground, complexNetwork, originalBitNetwork, pairedBitNetwork } from "./networks";
import { logIntegerEnclosure, expLowerBound, type Enclosure } from "./log";
import { noteParams, margins, marginsFromCostTable, minimumMargin, parameterChecks, holds, slack, type Check, type Params } from "./parameters";
import { guardChecks, guardConstants, unrolledDepthAtPower, unrolledDepth, leConstTimesPower, outerPhaseChargeSampled } from "./guard";
import { gaussianChecks, gaussianInstance } from "./gaussian";
import { buildPairedCircuit, PUBLISHED_CONVENTIONS, ALTERNATIVE_CONVENTIONS, type Conventions } from "./circuit";
import { verifyLocalCircuit } from "./verifyCircuit";
import { mergeGroups, verifyGlobal } from "./global";
import { checkMatching, exceptionalEigenvalue } from "./matching";
import { fixedNetworkCeiling, maxSideRoles, largestGridSaving } from "./ceiling";
import { binom } from "./intmath";
import {
  compactParams,
  compactParameterChecks,
  compactMarginChecks,
  compactStatedValues,
  compactMargins,
  compactMinimumMargin,
  layerExponents,
  type CompactParams,
} from "./compact/witness";
import { compactGuardChecks, compactGuardConstants, depthSamplesAtPowers } from "./compact/guard";
import { savingEnclosure } from "./compact/ceiling";
import { allocation, repairBound, digitIdentityExhaustive, guardWidth, ceilLog } from "./compact/layout";

export type Kind = "check" | "condition" | "constant" | "sample" | "identity" | "implied" | "observation";
export type Result = { section: string; name: string; source: string; ok: boolean; detail: string; kind: Kind };
/** Rows that are counted and decide the verdict. */
export const isCounted = (r: Result) => r.kind === "check" || r.kind === "condition" || r.kind === "constant" || r.kind === "sample";

const H = 50;
const TEN = (k: number) => 10n ** BigInt(k);
/** The bit saving certified by group B2 (paired-construction.tex prop:paired-bit-interface). */
export const BIT_SAVING = q(296n, TEN(11));

// ======================================================================= stated values

/** Numbers stated in notes/paired-construction.tex and 03-motifs.tex (patched to h = 50). */
export const STATED_BIT = {
  localAdditions: 9813n,
  localNonzero: 1271256n,
  c: 450394n,
  merged: 40256n,
  R: 509194n,
  v: 19600n,
  N: 7529536000000n,
  m: 125000n,
  I: 1152480000n,
  zb: 3243n,
  Wb: 73269972440000000n,
  sb: 9158746553232864000000n,
  LbOverN: q(75n, 196n),
  Wpair: 406321422080000n,
  spair: 50790175992864000000n,
  deficitPair: 1767136000000n,
  etaPair: q(23n, 661055000n),
  log2Power: 16n,
  L0: q(11737n, 1000n),
  aB: BIT_SAVING,
  eigenvalue: q(-41n, 9n), // 1 - h/9 at h = 50
};
/** Numbers stated for the preserved 2^-59 witness (paired-construction.tex, paired-note.tex). */
export const STATED_59 = {
  zc: 16356n,
  Wc: 369474390296480000n,
  sc: 46184298777878576000000n,
  LcOverN: q(153n, 392n),
  etaC: q(239n, 1202215191250n),
  G: q(272158569n, 156250000000000000000000000n),
  gammaExponent: q(1597n, 2000n),
  gridBit: 296n,
  gridComplex: 1n,
  widthConstant: 46n, // eq:gamma: gamma < 46 d^(3/2) sqrt b
};
/** Numbers stated for the compact-control witness (independent-complex.tex, compact-control-note.tex). */
export const STATED_COMPACT = {
  L0c: q(966n, 100n),
  m: 15625n,
  v: 2300n,
  N: 12167000000n,
  z: 1606n,
  W: 58645352620000n,
  L: 10315500000n,
  s: 916333630984500000n,
  eta: q(14n, 3464399375n),
  gammaExponent: q(15997n, 20000n),
  approxSaving: q(41847990372n, TEN(20)), // "approximately 4.1847990372e-10" (11 significant digits)
  ceilingDecimal: q(8369598075n, TEN(20)), // "8.369598075e-11"
  witnessFraction: q(99n, 100n), // "exceeds 99% of this upper enclosure"
  improvement: 47846242n, // current-status.md: "approximately 47,846,242 times" the 2^-59 saving (floor)
  widthConstant: 46n, // eq:gamma, retained
};
export type StatedBit = typeof STATED_BIT;
export type Stated59 = typeof STATED_59;
export type StatedCompact = typeof STATED_COMPACT;

// ======================================================================= helpers

function fromCheck(section: string, k: Check): Result {
  return { section, name: k.name, source: k.source, ok: holds(k), detail: `slack ${show(slack(k))}`, kind: k.kind ?? "check" };
}

function equals(section: string, name: string, source: string, got: bigint | Q | number, expected: bigint | Q | number, kind: Kind = "check"): Result {
  const g = typeof got === "object" ? show(got) : `${got}`;
  const e = typeof expected === "object" ? show(expected) : `${expected}`;
  return { section, name, source, ok: g === e, detail: g === e ? g : `got ${g}, note says ${e}`, kind };
}

function truth(section: string, name: string, source: string, ok: boolean, detail = "", kind: Kind = "check"): Result {
  return { section, name, source, ok, detail, kind };
}

type Timer = (label: string, t0: number) => void;
const noTimer: Timer = () => {};

/** Memoize the expensive, parameter-light computations (tests call the runners many times). */
const memo = new Map<string, unknown>();
function cached<T>(key: string, f: () => T): T {
  if (!memo.has(key)) memo.set(key, f());
  return memo.get(key) as T;
}

// ======================================================================= bit network (both witnesses)

export type BitOptions = {
  tick?: Timer;
  /** Summation conventions for the rebuilt circuit; the default reproduces the published counts. */
  conv?: Conventions;
  /** Also build the circuit under the alternative reading (the README observation; not in the verdict). Default true. */
  alternative?: boolean;
  stated?: Partial<StatedBit>;
};

/** The heavy part: circuit, merge, verification, matching, logarithm enclosure. */
export function computeBit(opts: BitOptions = {}) {
  const tick = opts.tick ?? noTimer;
  let t0 = performance.now();
  const local = buildPairedCircuit(H - 1, opts.conv ?? PUBLISHED_CONVENTIONS);
  const localReport = verifyLocalCircuit(local);
  const globalReport = verifyGlobal(mergeGroups(local, H));
  tick("circuit (published conventions)", t0);
  let alt: { local: ReturnType<typeof verifyLocalCircuit>; global: ReturnType<typeof verifyGlobal> } | undefined;
  if (opts.alternative ?? true) {
    t0 = performance.now();
    const altLocal = buildPairedCircuit(H - 1, ALTERNATIVE_CONVENTIONS);
    alt = { local: verifyLocalCircuit(altLocal), global: verifyGlobal(mergeGroups(altLocal, H)) };
    tick("circuit (alternative conventions)", t0);
  }
  t0 = performance.now();
  const match = checkMatching(H);
  tick("matching pi", t0);
  t0 = performance.now();
  const g = ground(H);
  const logm = logIntegerEnclosure(g.m, 24);
  const R = BigInt(globalReport.roles);
  tick("log enclosures (h=50)", t0);
  return { localReport, globalReport, alt, match, ground: g, originalBit: originalBitNetwork(H), pairedBit: pairedBitNetwork(H, R), R, logm };
}
export type BitValues = ReturnType<typeof computeBit> & { L0: Q };

export function bitRows(v: ReturnType<typeof computeBit>, st: StatedBit = STATED_BIT): Result[] {
  const out: Result[] = [];
  const { localReport, globalReport, match, ground: g, originalBit: b0, pairedBit: bp, logm } = v;
  const S = "B1 bit network: paired-block circuit [both witnesses]";
  const PC = "paired-construction.tex sec:paired-bit-construction";
  const PR = "paired-construction.tex, Reversible roles and frames";
  const q50 = BigInt(H) * binom(H - 1, 2);
  out.push(
    truth(S, "h = 50 is admissible: h > 6 (spare coordinates) and h != 9 (I - J/9 nondegenerate)", "parameter-note.tex; 03-motifs.tex", H > 6 && H !== 9, "", "constant"),
    equals(S, "local additions at n=49", PC, localReport.additions, st.localAdditions),
    equals(S, "local designated outputs = C(49,2)", PC + " (allocated as C(n,2))", localReport.outputs, 1176, "identity"),
    equals(S, "local nonzero coefficients", PC, localReport.nonzeroCoefficients, st.localNonzero),
    truth(S, "every local addition joins disjoint supports", PC, localReport.allAdditionsDisjoint),
    truth(S, "every local output support equals its definition (coefficients and zeros)", PC, localReport.allOutputSupportsExact),
    truth(S, "no unused local node", PC + " (remove unused nodes)", localReport.everyAdditionUsed),
    equals(S, "global additions c at h=50", PC, globalReport.additions, st.c),
    equals(S, "merged additions", PC, globalReport.mergedAdditions, st.merged),
    equals(S, "q = h C(h-1,2) partial outputs", PC + " (allocated as h C(h-1,2))", globalReport.partialOutputs, q50, "identity"),
    equals(S, "R = c + q side roles (identity applied to the recomputed c)", PR, globalReport.roles, st.R, "identity"),
    truth(S, "every global node has an outgoing use", PR, globalReport.everyNodeUsed),
    truth(S, "every global addition joins disjoint supports", PC, globalReport.allAdditionsDisjoint),
    truth(S, "every node's triples share a common point (U_z nondegenerate)", PR, globalReport.everyNodeHasCommonPoint),
    truth(S, "every partial output is exact (recomputed through merged decompositions)", PC, globalReport.allPartialOutputsExact),
    truth(S, "every output triple meets its target in one point (U_z within t_T^perp; implied by exactness, evaluated separately)", PR, globalReport.outputsOrthogonalToTarget, "", "implied"),
    truth(S, "pi is a bijection of the 19600 triples", PR, match.bijective && match.triples === 19600),
    truth(S, "|A cap pi(A)| = 1 for every triple", PR, match.intersectionOne),
    truth(S, "<t_A, t_pi(A)> = 0 in I - J/9, hence E within H", PR, match.joiningLabelsNested),
    equals(S, "exceptional eigenvalue 1 - h/9 = -41/9", "03-motifs.tex (patched)", exceptionalEigenvalue(H), st.eigenvalue, "constant"),
  );
  if (v.alt) {
    const a = v.alt;
    out.push(
      truth(
        "B0 observation (not part of either witness): the other reading of the circuit prose",
        "ceil split, zeros dropped, weights before edges: local and global support checks pass",
        "README, Conventions",
        a.local.allOutputSupportsExact &&
          a.local.allAdditionsDisjoint &&
          a.local.everyAdditionUsed &&
          a.global.allPartialOutputsExact &&
          a.global.allAdditionsDisjoint &&
          a.global.everyNodeHasCommonPoint &&
          a.global.everyNodeUsed &&
          a.global.outputsOrthogonalToTarget,
        `local ${a.local.additions}, c = ${a.global.additions}, merged = ${a.global.mergedAdditions}, R = ${a.global.roles}`,
        "observation",
      ),
    );
  }

  const N2 = "B2 bit network: counts and exponent tau = 1 - 296/10^11 [both witnesses]";
  const PB = "paired-construction.tex prop:paired-bit-interface";
  const M = "03-motifs.tex (patched to h=50)";
  const expL0 = cached(`exp ${show(st.L0)}`, () => expLowerBound(st.L0, 80));
  out.push(
    equals(N2, "v = C(50,3)", M, g.v, st.v),
    equals(N2, "N = v^3", M, g.N, st.N),
    equals(N2, "m = h^3", M, g.m, st.m),
    equals(N2, "I = 3 v^2", M, g.I, st.I),
    equals(N2, "z_b = 3 C(47,2)", M, b0.z, st.zb),
    equals(N2, "original W_b", M + " eq:bit-wire-count", b0.W, st.Wb),
    equals(N2, "original s_b", M + " prop:bit-motif-interface", b0.s, st.sb),
    equals(N2, "L_b / N", M, b0.lossOverN, st.LbOverN),
    equals(N2, "W_b^pair = 2N + 2v^2(R+h)", PB, bp.W, st.Wpair),
    equals(N2, "s_b^pair = W m - N + 6 v^2 h^2", PB, bp.s, st.spair),
    equals(N2, "W m - s > 0 (bit deficit)", PB, bp.deficit, st.deficitPair),
    equals(N2, "eta_b^pair", "paired-construction.tex, Explicit exponents", bp.eta, st.etaPair),
    equals(N2, "m = 2^16 * x with 1 <= x < 2", "paired-construction.tex: 16 log 2 + log(m/2^16)", BigInt(logm.k), st.log2Power),
    truth(N2, "e^L0 > m (Taylor partial sum, independent second route)", "parameter-note.tex method", lt(q(g.m), expL0), `partial sum ${toDecimal(expL0, 6)}`),
    fromCheck(N2, { name: "log m < L0 = 11737/1000", source: "paired-construction: 16(S(2)+E0(2)) + S(m/2^16)+E0(m/2^16) < L0", lhs: logm.upper, rel: "<", rhs: st.L0 }),
    fromCheck(N2, { name: "eta_b^pair > a_b L0, a_b = 296/10^11", source: "paired-construction: eta_b^pair > a L0", lhs: mul(st.aB, st.L0), rel: "<", rhs: bp.eta }),
  );
  return out;
}

export function bitNetwork(opts: BitOptions = {}) {
  const v = computeBit(opts);
  const st = { ...STATED_BIT, ...opts.stated };
  return { results: bitRows(v, st), values: { ...v, L0: st.L0 } as BitValues };
}

// ======================================================================= preserved 2^-59 witness

/** `h` replaces the ground size of the complex network (tests only; the bit network stays at h = 50). */
export type Options59 = { tick?: Timer; p?: Params; stated?: Partial<Stated59>; h?: number };

export function paired59(bit: BitValues, opts: Options59 = {}) {
  const tick = opts.tick ?? noTimer;
  const p = opts.p ?? noteParams();
  const st = { ...STATED_59, ...opts.stated };
  const out: Result[] = [];
  const { ground: g, pairedBit: bp, logm, R, L0 } = bit;
  const hc = opts.h ?? H;
  const cx = complexNetwork(hc);
  const mc = ground(hc).m; // = g.m at h = 50
  const b0 = bit.originalBit;
  const M = "03-motifs.tex (patched to h=50)";

  const CX = "P1 [2^-59] complex network at h = 50";
  out.push(
    equals(CX, "z_c = C(47,3) + 3*47", M, cx.z, st.zc),
    equals(CX, "W_c", M + " eq:complex-wire-count", cx.W, st.Wc),
    equals(CX, "s_c", M + " prop:complex-motif-interface", cx.s, st.sc),
    equals(CX, "L_c / N", M, cx.lossOverN, st.LcOverN),
    truth(CX, "L_b < N/2 and L_c < N/2", "audit.md: both losses satisfy L < N/2", lt(b0.lossOverN, q(1n, 2n)) && lt(cx.lossOverN, q(1n, 2n))),
    equals(CX, "eta_c", "paired-construction.tex, Explicit exponents", cx.eta, st.etaC),
    fromCheck(CX, { name: "eta_c > a_c L0, a_c = 1/10^11", source: "paired-construction: eta_c > a_c L0", lhs: mul(p.ac, L0), rel: "<", rhs: cx.eta }),
    fromCheck(CX, { name: "1 - tau <= a_b = 296/10^11 (bit saving certified in B2)", source: "paired-note.tex: tau = 1 - a, a = 296/10^11", lhs: sub(ONE, p.tau), rel: "<=", rhs: BIT_SAVING, kind: "condition" }),
  );

  const PA = "P2 [2^-59] parameters and final margin";
  const mg = margins(p);
  const G = minimumMargin(p);
  out.push(...parameterChecks(p).map((k) => fromCheck(PA, k)));
  out.push(
    truth(
      PA,
      "closed-form margins g1..g7 = 1 - (row exponent) of the patched cost table (two transcriptions agree)",
      "08-assembly cost table + eq:margin-list (patched)",
      Object.entries(marginsFromCostTable(p)).every(([k, x]) => eq(x, mg[k as keyof typeof mg])),
      "",
      "identity",
    ),
    equals(PA, "G = min g_j", "paired-note.tex sec. 4", G, st.G),
    truth(PA, "G = g2 = g3 = eps beta a^2", "paired-note.tex sec. 4 / paired-network.md", eq(G, mg.g2) && eq(G, mg.g3) && eq(G, mul(mul(p.epsilon, p.beta), mul(p.a, p.a)))),
    truth(PA, "G > 2^-59 (strict; the same comparison as kappa < G at kappa = 2^-59)", "paired-note.tex sec. 4", lt(twoPow(-59), G), `G / 2^-59 = ${toDecimal(div(G, twoPow(-59)), 10)} (display only)`, "implied"),
    truth(PA, "G < 2 * 2^-59 (so the old half-margin rule is NOT met)", "witness.all_margins_at_least_twice_kappa = false", lt(G, twoPow(-58))),
    equals(PA, "tau(1+c/beta) = 1 - a^2 (recipe c = beta a)", "patched 08-assembly", mul(p.tau, add(ONE, div(p.c, p.beta))), sub(ONE, mul(p.a, p.a)), "identity"),
  );

  const GU = "P3 [2^-59] stopped guard (beta = 999/1000, C1 = 2)";
  const gc = guardConstants(cx.W, cx.s, mc);
  out.push(...guardChecks(cx.W, cx.s, mc, p.beta, p.C1).map((k) => fromCheck(GU, k)));
  out.push(truth(GU, "8d + floor(D/2) + 9 <= 18d for 1 <= D <= d <= 10^5 (sampled; true for every d >= 1)", "stopped-guard.tex", cached("outer", () => outerPhaseChargeSampled(100000)), "", "identity"));
  let t0 = performance.now();
  const depth = cached(`depth59 ${hc} ${show(p.beta)}`, () => depthSamples(mc, cx.s, gc.E, gc.B, p.beta));
  tick("guard depth recurrence samples (2^-59)", t0);
  out.push(truth(GU, "unrolled depth recurrence obeys both stated bounds on all samples", "stopped-guard.tex", depth.ok, depth.detail));

  const GA = "P4 [2^-59] Gaussian width (eps = 199/1000)";
  const GSRC = "paired-note.tex sec. 3 / eq:gamma (h50-paired-59.patch)";
  out.push(...gaussianChecks(p.epsilon, st.gammaExponent, GSRC, st.widthConstant).map((k) => fromCheck(GA, k)));
  t0 = performance.now();
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`gauss ${e} ${show(p.epsilon)}`, () => gaussianInstance(e, p.epsilon));
    out.push(truth(GA, `b = 2^${e}: alpha, gamma meet every stated bound`, "paired-note.tex sec. 3", r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }
  tick("Gaussian instances (2^-59)", t0);

  const RO = "P5 [2^-59] room left";
  const ceil = fixedNetworkCeiling(bp.eta, logm.lower);
  const Rmax = maxSideRoles(H, p.a, L0);
  out.push(
    truth(RO, "fixed-network ceiling a^2/(5(1-a)) < 2^-58", "paired-network.md / fixed_network_ceiling", lt(ceil.value, twoPow(-58)), `ceiling / 2^-59 = ${toDecimal(div(ceil.value, twoPow(-59)), 6)}`),
    truth(RO, "R is within the role budget for the witness's a_b", "derived from prop:paired-bit-interface", R <= Rmax, `R = ${R}, largest admissible R = ${Rmax}`),
    equals(RO, "largest bit saving on the 10^-11 grid", "derived", largestGridSaving(bp.eta, L0, TEN(11)), st.gridBit),
    equals(RO, "largest complex saving on the 10^-11 grid", "derived", largestGridSaving(cx.eta, L0, TEN(11)), st.gridComplex),
  );

  return {
    results: out,
    values: {
      complex: cx,
      params: p,
      margins: mg,
      G,
      guard: gc,
      ceiling: ceil,
      Rmax,
      bitDeficitSlack: sub(bp.eta, mul(p.a, L0)),
      complexDeficitSlack: sub(cx.eta, mul(p.ac, L0)),
      parameterChecks: parameterChecks(p),
    },
  };
}

/**
 * Samples of the unrolled guard recurrence (2^-59 witness). For each d >= 2 and each root e = m^k <= d,
 * check  j <= (1-beta) log_m d + 1,  A <= s(8+E) d^(5-4beta),  A <= 9 B^2 d^(7/5).
 * Exact powers d = m^K with 250 | K let the fractional powers be computed exactly
 * (d^(251/250) = d * m^(K/250), d^(7/5) = d * m^(2K/5)); several have j = 2, 3, 4.
 * The exact-power samples are defined for beta = 999/1000 only; for another beta the
 * function reports failure rather than evaluating a different statement.
 */
export function depthSamples(m: bigint, s: bigint, E: bigint, B: bigint, beta: Q) {
  const onePiece = sub(q(5n), mul(q(4n), beta)); // 251/250 for beta = 999/1000
  if (onePiece.den !== 250n || onePiece.num !== 251n) return { ok: false, detail: "samples are defined for the witness's beta = 999/1000 only" };
  const C1 = s * (8n + E);
  const C2 = 9n * B * B;
  let ok = true;
  let cases = 0;
  let maxJ = 0;
  for (const d of [2n, 3n, 10n, 1000n, m - 1n, m, m + 1n, m * m, m * m * m + 7n]) {
    for (let k = 0; m ** BigInt(k) <= d; k++) {
      const { A, j } = unrolledDepth(k, d, m, s, E, beta);
      cases++;
      maxJ = Math.max(maxJ, j);
      // j <= (1-beta) log_m d + 1  <=>  m^((j-1) v) <= d^(v-u)   for beta = u/v
      const jOk = j === 0 || m ** (BigInt(j - 1) * beta.den) <= d ** (beta.den - beta.num);
      if (!(jOk && leConstTimesPower(A, C1, d, onePiece) && leConstTimesPower(A, C2, d, q(7n, 5n)))) ok = false;
    }
  }
  for (const K of [250, 1000, 1250, 2000, 3000, 4000]) {
    const Lmin = Math.max(0, Math.floor((999 * K) / 1000) - 2);
    for (let k = Lmin; k <= K; k++) {
      const { A, j } = unrolledDepthAtPower(k, K, m, s, E, beta);
      cases++;
      maxJ = Math.max(maxJ, j);
      const jOk = j === 0 || 1000 * (j - 1) <= K;
      const d = m ** BigInt(K);
      const b1 = C1 * d * m ** BigInt(K / 250); // s(8+E) d^(251/250)
      const b2 = C2 * d * m ** BigInt((2 * K) / 5); // 9 B^2 d^(7/5)
      if (!(jOk && A <= b1 && A <= b2)) ok = false;
    }
  }
  return { ok, detail: `${cases} roots, up to ${maxJ} internal levels` };
}

// ======================================================================= current compact-control witness

export const COMPLEX_H = 25;
export const L0_COMPLEX = STATED_COMPACT.L0c; // independent-complex.tex: log m_c < 966/100

/** The checks of one compact-control parameter set with its complex network at ground size h. */
export function compactWitnessChecks(p: CompactParams, h: number) {
  const cx = complexNetwork(h);
  const m = ground(h).m;
  const logm = logIntegerEnclosure(m, 24);
  const guard = compactGuardConstants(cx.W, cx.s, m, p.zeta);
  const enclosure = savingEnclosure(cx.eta, logm);
  return {
    cx,
    m,
    logm,
    guard,
    enclosure,
    exponents: layerExponents(p),
    margins: compactMargins(p),
    G: compactMinimumMargin(p),
    parameterChecks: compactParameterChecks(p),
    marginChecks: compactMarginChecks(p),
    guardChecks: compactGuardChecks(cx.W, cx.s, m, p.beta, p.zeta, p.C1),
    complexSupported: lt(p.ac, enclosure.lower), // a_c below the enclosure of the actual saving
  };
}

/** `h` replaces the complex ground size h_c = 25 (tests only: every row is then re-evaluated for that network). */
export type OptionsCompact = { tick?: Timer; p?: CompactParams; stated?: Partial<StatedCompact>; h?: number };

/** Own layout instances: d = 10^k, K = floor(d^(1/5)), p = 2^(5 ceil(log2 d)) (so d ~ p^(1/5)). */
function layoutInstances(m: bigint, W: bigint) {
  return [3, 6, 12, 30].map((k) => {
    const d = TEN(k);
    let K = 1n;
    while ((K + 1n) ** 5n <= d) K++;
    const p0 = 1n << BigInt(5 * ceilLog(d, 2n));
    const Gw = BigInt(guardWidth(p0));
    const al = allocation(d, d, K, Gw, m, W);
    const ok = al.rowRangeCoversWk0 && al.frontFieldsFit && al.backFieldFits && al.reservedCountBound && (2n * K) ** 5n >= d;
    return { k, K, Gw, al, ok };
  });
}

function repairSweep(pMax: bigint) {
  let ok = true;
  let cases = 0;
  for (let pp = 2n; pp <= pMax; pp++) {
    const lg = BigInt(ceilLog(pp, 2n)); // ceil(log2 p)
    const G0 = BigInt(guardWidth(pp));
    const r = repairBound(pp, pp, G0 + 4n * lg + 10n);
    cases++;
    if (!(r.cutoff && r.ok)) ok = false;
  }
  return { ok, cases };
}

export function compact(_bit: BitValues | undefined, opts: OptionsCompact = {}) {
  const tick = opts.tick ?? noTimer;
  const p = opts.p ?? compactParams();
  const st = { ...STATED_COMPACT, ...opts.stated };
  const out: Result[] = [];
  const hc = opts.h ?? COMPLEX_H;
  const w = compactWitnessChecks(p, hc);
  const { cx, m, logm } = w;
  const g = ground(hc);
  const IC = "independent-complex.tex prop:compact-complex-interface";

  const CX = "C1 [compact] complex network at h_c = 25";
  let t0 = performance.now();
  const expL0c = cached(`exp ${show(st.L0c)}`, () => expLowerBound(st.L0c, 60));
  tick("log enclosures (h=25)", t0);
  out.push(
    truth(CX, "h_c = 25 > 6 (a coordinate outside six; 3^j < 25^j)", IC, hc > 6, "", "constant"),
    equals(CX, "m_c = 25^3", IC, m, st.m),
    equals(CX, "v_c = C(25,3)", IC, g.v, st.v),
    equals(CX, "N_c = v_c^3", IC, g.N, st.N),
    equals(CX, "z_c = C(22,3) + 66", IC, cx.z, st.z),
    equals(CX, "W_c = 2 v^3 + 3 v^2 (v z_c + 26)", IC, cx.W, st.W),
    equals(CX, "L_c = 3 v^2 * 25 * 26", IC, cx.L, st.L),
    equals(CX, "s_c = W_c m_c - 2 N_c + 2 L_c", IC, cx.s, st.s),
    equals(CX, "eta_c = (W_c m_c - s_c)/(W_c m_c)", IC, cx.eta, st.eta),
    truth(CX, "L_c < N_c (the positivity the note needs)", IC, cx.L < g.N, `L_c/N_c = ${show(cx.lossOverN)}`),
    truth(CX, "2 L_c < N_c fails at h = 25 (the note says it is not needed)", IC, !(2n * cx.L < g.N)),
    truth(CX, "e^(966/100) > m_c (Taylor partial sum, independent second route)", "independent-complex.tex: log m_c < 966/100", lt(q(m), expL0c)),
    fromCheck(CX, { name: "log m_c < 966/100 (atanh enclosure, 24 terms)", source: "independent-complex.tex", lhs: logm.upper, rel: "<", rhs: st.L0c }),
    fromCheck(CX, { name: "eta_c > a_c (966/100), a_c = 418/10^12", source: IC, lhs: mul(p.ac, st.L0c), rel: "<", rhs: cx.eta }),
    fromCheck(CX, { name: "eta_c > a_c log_upper(m_c) (certificate's form; implied by the row above since log_upper < 966/100)", source: "compact-control-layer.json complex_deficit_slack", lhs: mul(p.ac, logm.upper), rel: "<", rhs: cx.eta, kind: "implied" }),
  );

  const B = "C2 [compact] bit exponent used by the swaps";
  out.push(
    fromCheck(B, {
      name: "1 - tau <= a_b = 296/10^11 (bit saving certified in B2)",
      source: "compact-control-note.tex sec. Scope: tau = 1 - 296/10^11",
      lhs: sub(ONE, p.tau),
      rel: "<=",
      rhs: BIT_SAVING,
      kind: "condition",
    }),
  );

  const PA = "C3 [compact] parameters, layer exponents, margins";
  out.push(...w.parameterChecks.map((k) => fromCheck(PA, k)));
  for (const r of compactStatedValues(p)) out.push(equals(PA, r.name, r.source, r.got, r.stated));
  out.push(...w.marginChecks.map((k) => fromCheck(PA, k)));
  out.push(
    truth(
      PA,
      "closed-form margins g1..g7 = 1 - (row exponent) of the patched cost table (two transcriptions agree)",
      "compact-control-34.patch 08-assembly cost table + eq:margin-list",
      Object.entries(marginsFromCostTable(p)).every(([k, x]) => eq(x, w.margins[k as keyof typeof w.margins])),
      "",
      "identity",
    ),
  );

  const GU = "C4 [compact] generalized guard (beta = 1/1000, zeta = 1/10000)";
  out.push(...w.guardChecks.map((k) => fromCheck(GU, k)));
  out.push(truth(GU, "8d + floor(D/2) + 9 <= 18d for 1 <= D <= d <= 10^5 (sampled; true for every d >= 1)", "compact-control-guard.tex", cached("outer", () => outerPhaseChargeSampled(100000)), "", "identity"));
  t0 = performance.now();
  const depth = cached(`depthC ${hc} ${show(p.beta)} ${show(p.zeta)}`, () => {
    try {
      return depthSamplesAtPowers([250, 500, 1000, 1250, 2000], m, cx.s, w.guard.E, w.guard.B, p.beta);
    } catch (e) {
      return { ok: false, detail: String(e) };
    }
  });
  tick("guard depth recurrence samples (compact)", t0);
  out.push(truth(GU, "unrolled recurrence: j <= (1-beta) log_m d + 1 and A <= s(8+E) d^(5-4beta) (<= 9B^2 d^(5-4beta) follows)", "compact-control-guard.tex", depth.ok, depth.detail));

  const GA = "C5 [compact] Gaussian width (eps = 1999/10000)";
  const GSRC = "compact-control-note.tex sec. Parameters / compact-control-34.patch eq:gamma";
  // The two "gamma exponent ... stated" rows repeat the C3 equality "gamma exponent 1/2 + 3 eps/2 = 15997/20000".
  const dupOfC3 = (k: Check): Check => (k.name.startsWith("gamma exponent 1/2 + 3 eps/2") ? { ...k, kind: "implied", source: k.source + " (same as the C3 row)" } : k);
  out.push(...gaussianChecks(p.epsilon, st.gammaExponent, GSRC, st.widthConstant).map((k) => fromCheck(GA, dupOfC3(k))));
  out.push(
    fromCheck(GA, {
      name: "eps < 1/5 (used for the cutoff, and for the ceiling)",
      source: GSRC + ": since eps < 1/5 (implied by 3/4 + delta + 5 eps/4 < 1 with delta > 0)",
      lhs: p.epsilon,
      rel: "<",
      rhs: q(1n, 5n),
      kind: "implied",
    }),
    fromCheck(GA, { name: "184 < 2^8 = 2^(40/5)", source: GSRC + ": indeed 184 < 2^8", lhs: q(184n), rel: "<", rhs: q(256n), kind: "constant" }),
  );
  t0 = performance.now();
  for (const e of [40, 41, 48, 64, 100]) {
    const r = cached(`gauss ${e} ${show(p.epsilon)}`, () => gaussianInstance(e, p.epsilon));
    out.push(truth(GA, `b = 2^${e}: alpha, gamma meet every stated bound`, GSRC, r.ok, `d=${r.d} alpha=${r.alpha} gamma=${r.gamma}`));
  }
  tick("Gaussian instances (compact)", t0);

  const CE = "C6 [compact] complex saving and scoped ceiling";
  const enc: Enclosure = w.enclosure;
  const upper5 = div(enc.upper, q(5n));
  const NOTEC = "compact-control-note.tex, Earlier targets and the next ceiling";
  const halfUlp = q(5n, TEN(21)); // half a unit in the last stated digit of 4.1847990372e-10
  out.push(
    truth(CE, "a_c < lower enclosure of the actual saving a* = -log(1-eta_c)/log m_c (second route: Mercator series)", IC, w.complexSupported, `a* in [${toDecimal(enc.lower, 22)}, ${toDecimal(enc.upper, 22)}]`),
    truth(
      CE,
      "actual saving is approximately 4.1847990372e-10 (the whole enclosure rounds to it)",
      NOTEC,
      le(sub(st.approxSaving, halfUlp), enc.lower) && lt(enc.upper, add(st.approxSaving, halfUlp)),
    ),
    // The ceiling argument is symbolic: g5 > 0 gives eps < 1/5; the leaf condition gives
    // 1 - lambda' < (1-beta)(1-sigma) < 1 - sigma = a_c < a*; so kappa < g3 = eps(1-lambda') < a*/5
    // for EVERY parameter set satisfying group C3. Its only finite content is the enclosure of a*
    // and the comparisons below. On the witness the chain reads:
    fromCheck(CE, { name: "chain on the witness: kappa < g3 = eps(1-lambda') < a_c/5 (implied by C3, C5)", source: NOTEC, lhs: w.margins.g3, rel: "<", rhs: div(p.ac, q(5n)), kind: "implied" }),
    fromCheck(CE, { name: "a*/5 <= upper/5 < 8.369598075e-11 (stated decimal)", source: NOTEC, lhs: upper5, rel: "<", rhs: st.ceilingDecimal }),
    fromCheck(CE, { name: "8.369598075e-11 < 2^-33", source: NOTEC, lhs: st.ceilingDecimal, rel: "<", rhs: twoPow(-33), kind: "constant" }),
    fromCheck(CE, { name: "witness exceeds 99% of the upper enclosure: kappa > (99/100) upper/5", source: NOTEC, lhs: mul(st.witnessFraction, upper5), rel: "<", rhs: p.kappa }),
    equals(CE, "floor(kappa * 2^59) (improvement over the published 2^-59)", "current-status.md: approximately 47,846,242 times", mul(p.kappa, twoPow(59)).num / mul(p.kappa, twoPow(59)).den, st.improvement),
  );

  const LA = "C7 [compact] layout and repair arithmetic (own instances; lemma samples, independent of the witness)";
  t0 = performance.now();
  for (const x of cached(`layout ${m} ${cx.W}`, () => layoutInstances(m, cx.W)))
    out.push(
      truth(
        LA,
        `d = 10^${x.k}, K = floor(d^(1/5)) = ${x.K}, G = ${x.Gw}: field capacities, 2^(q0 K) >= W^k0, q_F + q_B <= 3dG/K + 2, K >= d^c/2`,
        "compact-control-layout.tex (true for every d, K >= 1 by the ceilings in the definitions)",
        x.ok,
        `mode ${x.al.mode}, Q0 = ${x.al.reserved_chunks}`,
        "identity",
      ),
    );
  const rep = cached("repair 4096", () => repairSweep(4096n));
  out.push(
    truth(LA, "delta = n(2*2^-G + 8*2^(G-K)) <= 5/(128 p^3) at the cutoff K = G + 4 ceil(log2 p) + 10, n = p, p = 2..4096", "compact-control-movement.tex prop:compact-selected-addition", rep.ok, `${rep.cases} values of p`, "sample"),
    // For every p: 2^-G <= p^-4/64 and 2^(G-K) <= p^-4/1024 at the cutoff, so delta <= n p^-4 (2/64 + 8/1024).
    equals(LA, "2/64 + 8/1024 = 5/128 (the constant of the general step, all p >= 2)", "compact-control-movement.tex prop:compact-selected-addition", add(q(2n, 64n), q(8n, 1024n)), q(5n, 128n), "constant"),
  );
  const dig = cached("digits", () => digitIdentityExhaustive(40, 4));
  out.push(
    truth(LA, "four-update identity: final v = v + z(1-2a), dirty temporary restored (all v, w in [-40,40])", "compact-control-movement.tex, Earlier source", dig.identity, "", "sample"),
    truth(LA, "good digits (w <= B-2): load stays in its digit; target displacement at most 2B (G = 1..4)", "compact-control-movement.tex, Guards and deterministic repair", dig.loadWithinDigit && dig.displacementWithin2B, "", "sample"),
    truth(LA, "later source: control parities differ by exactly x; temporaries restored (G = 1..4)", "compact-control-movement.tex, Later source", dig.laterSourceParity, `${dig.cases} cases`, "sample"),
  );
  tick("layout and digit arithmetic", t0);

  return { results: out, values: { params: p, witness: w, ground: g } };
}
