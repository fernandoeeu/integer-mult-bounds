// Cross-PR observations. SPECULATION, not claims of any PR and not part of any
// verdict: what the recomputed numbers say about combining the PRs. Every row
// here has kind "observation".
//
//  X1  PR 1's beta with PR 2's bit saving a = 305/10^11 (both on base bcd4ebd):
//      the leaf condition (1 - beta) b > beta a^2 decides whether they compose as is.
//  X2  PR 1's scoped supremum recomputed at a = 305/10^11.
//  X3  PR 3 or PR 4's complex network with PR 2's bit network in the compact-control
//      system. PR 3 and PR 4 are bit-limited (kappa < a/5); a larger a raises that
//      ceiling. A candidate parameter set is checked against the same conditions.
//      This assumes, without any check here, that the compact-control construction
//      accepts PR 2's aligned bit network unchanged (PR 2 was written against bcd4ebd).

import { q, sub, mul, div, lt, le, ONE, toDecimal, show, type Q } from "../rational";
import { parameterChecks } from "../parameters";
import { compactParameterChecks, compactMinimumMargin, type CompactParams } from "../compact/witness";
import { recipe, supremumBySqrt } from "./pr1";
import { truth, type Result } from "./rows";
import { compactGuardChecks } from "../compact/guard";
import { fastParameterChecks, fastMinimumMargin, guardBetaThreshold } from "./fastGaussian";
import { pr5Params } from "./pr5";
import { pr6Params } from "./pr6";
import { sharedRetainedNetwork, STATED_PR4B } from "./pr4b";
import { compressedNetwork, STATED_PR3 } from "./pr3";

const TEN = (k: number) => 10n ** BigInt(k);
const SX = "X cross-PR SPECULATION (not a claim of any PR; not in any verdict)";

export function cross(): Result[] {
  const out: Result[] = [];
  const holds = (k: { lhs: any; rel: "<" | "<="; rhs: any }) => (k.rel === "<" ? lt(k.lhs, k.rhs) : le(k.lhs, k.rhs));

  // X1
  const a2 = q(305n, TEN(11));
  const p1 = recipe(a2, q(1n, TEN(11)), q(99999912384n, TEN(11)), q(1999999999999n, TEN(13)), q(1n, TEN(14)), q(17523184n, TEN(25)));
  const fail1 = parameterChecks(p1).filter((k) => !holds(k)).map((k) => k.name);
  out.push(truth(SX, "X1 PR 1's parameters with PR 2's a = 305/10^11: all 2^-59-system conditions hold", "speculation", fail1.length === 0, fail1.length ? `fails: ${fail1.join("; ")}` : "all hold", "observation"));

  // X2
  const sup = supremumBySqrt(a2, q(1n, TEN(11)));
  out.push(truth(SX, "X2 PR 1's scoped supremum G_* at a = 305/10^11 (2^-59-type system, b = 1/10^11, C1 = 2)", "speculation", true, `G_* in [${toDecimal(mul(sup.G.lower, q(TEN(18))), 12)}, ${toDecimal(mul(sup.G.upper, q(TEN(18))), 12)}] e-18`, "observation"));

  // X3
  for (const [label, ac] of [
    ["PR 3 complex network (a_c = 14/10^9)", q(14n, TEN(9))],
    ["PR 4 complex network (a_c = 750/10^11)", q(750n, TEN(11))],
  ] as const) {
    const p: CompactParams = {
      a: a2,
      ac,
      tau: sub(ONE, a2),
      sigma: sub(ONE, ac),
      epsilon: q(1999n, 10000n),
      c: q(1n),
      beta: q(1n, 1000n),
      zeta: q(1n, 10000n),
      delta: q(1n, TEN(6)),
      C1: q(49961n, 10000n),
      lambda: sub(ONE, q(3049n, TEN(12))),
      lambdaPrime: sub(ONE, q(3048n, TEN(12))),
      kappa: q(609n, TEN(12)),
    };
    const G = compactMinimumMargin(p);
    const fail = compactParameterChecks(p).filter((k) => !holds(k)).map((k) => k.name);
    if (!lt(p.kappa, G)) fail.push("kappa < G_*");
    out.push(
      truth(
        SX,
        `X3 ${label} + PR 2 bit network (a = 305/10^11): candidate kappa = 609/10^12 with lambda' = 1 - 3048/10^12, c = 1`,
        "speculation",
        fail.length === 0,
        `${fail.length ? "fails: " + fail.join("; ") : "all compact conditions hold"}; G_* = ${toDecimal(mul(G, q(TEN(12))), 4)}e-12; ceiling a/5 = ${toDecimal(mul(div(a2, q(5n)), q(TEN(12))), 1)}e-12`,
        "observation",
      ),
    );
  }
  return out;
}

// ---------------------------------------------------------------------------
// Cross-PR observations for PRs 4b, 5 and 6 (8 October 2026). SPECULATION, not claims
// of any PR and not part of any verdict. PR 4b (head 8c225e6) is written against the
// retained-complex branch; PRs 5 and 6 against PR 3's compressed network. These rows
// assume, without any check here, that PR 5's resampling and PR 6's bit network do not
// interact with the complex producer except through its constants m, W, s and a_c
// (the guard and the leaf condition).
//
//  X4  PR 4b's complex network (h = 24, a_c = 2970/10^11) in PR 5's fast assembly.
//  X5  The same with PR 6's bit network (a = 325/10^11) at kappa = 1624/10^12.
//  X6  Where the leaf-and-guard window for a larger bit saving closes, with each
//      complex network (PR 6's doc: "A further 3% on a_b would close this window").
//  X7  s_c < m_c^4 for both complex networks (PR 6's doc mentions C1 = 4 - 3 beta).


export function cross2(): Result[] {
  const out: Result[] = [];
  const SX2 = "X2 cross-PR SPECULATION, PRs 4b to 6 (not a claim of any PR; not in any verdict)";
  const holds = (k: { lhs: any; rel: "<" | "<="; rhs: any }) => (k.rel === "<" ? lt(k.lhs, k.rhs) : le(k.lhs, k.rhs));
  const nw4b = sharedRetainedNetwork(24, STATED_PR4B.R);
  const ac4b = q(2970n, TEN(11));
  for (const [label, base] of [
    ["X4 PR 4b complex network + PR 5 fast assembly (a = 296/10^11, kappa = 1479/10^12)", pr5Params()],
    ["X5 PR 4b complex network + PR 6 bit network + fast assembly (a = 325/10^11, kappa = 1624/10^12)", pr6Params()],
  ] as const) {
    const p = { ...base, ac: ac4b, sigma: sub(ONE, ac4b) };
    const fail = fastParameterChecks(p).filter((k) => !holds(k)).map((k) => k.name);
    const G = fastMinimumMargin(p);
    if (!lt(p.kappa, G)) fail.push("kappa < G_*");
    const gfail = compactGuardChecks(nw4b.W, nw4b.s, nw4b.m, p.beta, p.zeta, p.C1).filter((k) => !holds(k)).map((k) => k.name);
    out.push(truth(SX2, label, "speculation", fail.length + gfail.length === 0, `${fail.length + gfail.length ? "fails: " + [...fail, ...gfail].join("; ") : "all fast-assembly conditions and the guard (m = 13824, W, s of PR 4b) hold"}; G_* = ${show(G)}, unchanged: still bit-limited (kappa < a/2)`, "observation"));
  }
  const p6 = pr6Params();
  const thr = guardBetaThreshold(p6);
  for (const [label, ac] of [
    ["PR 3 network (a_c = 14/10^9)", q(14n, TEN(9))],
    ["PR 4b network (a_c = 2970/10^11)", ac4b],
  ] as const)
    out.push(
      truth(
        SX2,
        `X6 window for a larger bit saving with the ${label}: a < (1 - beta) a_c`,
        "speculation",
        true,
        `beta = 19/25: a < ${toDecimal(mul(mul(sub(ONE, p6.beta), ac), q(TEN(11))), 2)}/10^11; beta at the guard threshold: a < ${toDecimal(mul(mul(sub(ONE, thr), ac), q(TEN(11))), 2)}/10^11`,
        "observation",
      ),
    );
  const nw3 = compressedNetwork(25, STATED_PR3.R);
  out.push(truth(SX2, "X7 s_c < m_c^4 for PR 3's and PR 4b's complex networks (PR 6's doc: C1 = 4 - 3 beta would then be available; not used by any PR)", "speculation", nw3.s < nw3.m ** 4n && nw4b.s < nw4b.m ** 4n, `PR 3: s/m^4 = ${toDecimal(q(nw3.s, nw3.m ** 4n), 3)}; PR 4b: ${toDecimal(q(nw4b.s, nw4b.m ** 4n), 3)}`, "observation"));
  return out;
}

// ------------------------------------------------------------------ X3: PRs 14 to 16 (8 October, later)
// Observations and SPECULATION only (kind "observation", never in a verdict):
//  - PR 15 and PR 16 both batch every complex residual of PR 7's h = 28 network, with
//    histograms built by their own schedules. They are compared rank by rank, and each
//    PR's complex saving is evaluated on the other's histogram.
//  - PR 16's nested exit corner and the two data blocks (PR 14, PR 16) applied to PR 15's
//    smaller h = 30 producer (R = 13056812): the largest a_b the moment would then certify.
//    This assumes the lemmas carry over to PR 15's reused registers, which nobody claims.
import { histogramClasses, histogramRankSum } from "./allResiduals";
import { PR15_HISTOGRAM, STATED_PR15 } from "./pr15";
import { pr16Histogram, pr16Classes, STATED_PR16 } from "./pr16";
import { pr14Classes } from "./pr14";
import { primeFieldBitNetwork, primeFieldComplexNetwork } from "./pr7";
import { momentWeights, momentUpperSecond, largestGridSaving } from "./batched";

export function cross3(): Result[] {
  const out: Result[] = [];
  const S3 = "X3 cross-PR observations and SPECULATION, PRs 14 to 16 (not a claim of any PR; not in any verdict)";
  const cn = primeFieldComplexNetwork(28, 93838n);
  const h15 = new Map(PR15_HISTOGRAM);
  const h16 = pr16Histogram(cn.v, 28n, STATED_PR16.Bc);
  const keys = [...new Set([...h15.keys(), ...h16.keys()])].sort((a, b) => (a < b ? -1 : 1));
  const diffs = keys.filter((r) => (h15.get(r) ?? 0n) !== (h16.get(r) ?? 0n)).map((r) => `rank ${r}: ${(h15.get(r) ?? 0n) - (h16.get(r) ?? 0n)}`);
  out.push(
    truth(S3, "PR 15's (certificate) and PR 16's (note) complex histograms: both rank sums equal s", "derived", histogramRankSum(h15) === cn.s && histogramRankSum(h16) === cn.s, `${histogramRankSum(h15)}`, "observation"),
    truth(S3, "where they differ (PR 15 minus PR 16 copies); N = v^3", "derived", true, `${diffs.join("; ")}; N = ${cn.N}; 27 + 729 = 756`, "observation"),
  );
  const moment = (hist: Map<bigint, bigint>, a: Q) => momentUpperSecond(momentWeights(cn.m, cn.W, cn.s, histogramClasses(hist)).items, a).bound;
  out.push(
    truth(S3, "PR 15's a_c = 4191487/10^12 on PR 16's histogram (second route): Xi < 1", "derived", lt(moment(h16, STATED_PR15.ac), ONE), "", "observation"),
    truth(S3, "PR 16's a_c = 4/10^6 on PR 15's histogram (second route): Xi < 1", "derived", lt(moment(h15, STATED_PR16.ac), ONE), "", "observation"),
  );
  const gC = largestGridSaving(momentWeights(cn.m, cn.W, cn.s, histogramClasses(h16)).items, 10n ** 12n, 4191487n);
  out.push(truth(S3, "largest a_c on the 10^-12 grid with PR 16's histogram (second route); PR 15's histogram gives 4191516 there", "derived", true, `${gC.k}/10^12`, "observation"));
  // PR 15's producer with PR 14's data blocks and PR 16's nested exit corner (h = 30)
  const bn = primeFieldBitNetwork(30, STATED_PR15.R);
  const combos: [string, ReturnType<typeof pr16Classes>][] = [
    ["PR 15 + PR 14's two data blocks", pr14Classes(30n, bn.v, STATED_PR15.R)],
    ["PR 15 + data blocks + PR 16's nested exit corner", pr16Classes(30n, bn.v, STATED_PR15.R)],
  ];
  for (const [name, cls] of combos) {
    const g = largestGridSaving(momentWeights(bn.m, bn.W, bn.s, cls).items, 10n ** 12n, 2153359n);
    out.push(truth(S3, `speculation: ${name}: largest a_b on the 10^-12 grid (second route; PR 15 states 2153359)`, "derived", true, `${g.k}/10^12 = ${toDecimal(q(g.k, 10n ** 12n), 12)}`, "observation"));
  }
  return out;
}
