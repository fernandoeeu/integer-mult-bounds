// Field-by-field comparison of the recomputed PR values with each PR's own JSON
// certificate. Run only after the recomputation (`bun run check:prs`); the
// certificates are never used as inputs to the checks.
//   bun run compare:prs [--only=1,3]
// The certificates are copies of the PR heads' files, in prs/certificates/
// (commits and sha256 in prs/certificates/SOURCES.txt). Statuses as in
// src/comparator.ts. Exit code 1 on any disagreement.

import { createHash } from "node:crypto";
import { type Q, q, parseQ, eq, sub, add, mul, div, le, lt, twoPow, ONE, toDecimal, show } from "../rational";
import { slack, margins as margins59, minimumMargin, parameterChecks, noteParams, type Params } from "../parameters";
import { compactParameterChecks, type CompactParams } from "../compact/witness";
import { Comparator } from "../comparator";
import { maxSideRoles } from "../ceiling";
import { ground, complexNetwork } from "../networks";
import { pr1, pr1DesignParams } from "./pr1";
import { pr2 } from "./pr2";
import { pr3 } from "./pr3";
import { pr4 } from "./pr4";
import { pr4b } from "./pr4b";
import { pr5 } from "./pr5";
import { pr6 } from "./pr6";
import { fastParameterChecks, fastWidthInstance, stepExcess } from "./fastGaussian";
import { pr7 } from "./pr7";
import { pr8, bitScreen } from "./pr8";
import { buildPairedTriple } from "./pairedTriple";
import { mergeProducers, prune } from "./primeField";
import { dyadicCircuit, disjointRequests, intersectionTwoRequests } from "./geometric";
import { binom } from "../intmath";
import { pr9 } from "./pr9";
import { pr10, STATED_PR10 } from "./pr10";
import { pr11 } from "./pr11";
import { pr12, STATED_PR12 } from "./pr12";
import { pr13, STATED_PR13 } from "./pr13";
import { pr14, STATED_PR14 } from "./pr14";
import { pr15, STATED_PR15, PR15_HISTOGRAM } from "./pr15";
import { pr16, STATED_PR16 } from "./pr16";
import { momentUpperBound } from "./batched";
import { primeFieldBitNetwork } from "./pr7";
import { bulkPathBounds, bulkGuardConstants, slackTable, logInverseEnclosure } from "./batched";
import { compactGuardConstants as compactGuardConstantsFor } from "../compact/guard";

const dir = `${import.meta.dir}/../../prs/certificates`;
// Optional: a local clone containing the pinned PR 4 commits (42a88ef, 8c225e6), used only to
// recompute PR 4's proof_sha256 file hashes. Without it those fields are not compared.
const CLONE = process.env.PR_CLONE;

/** JSON without precision loss (as src/comparator.ts), but a decimal number is kept as its literal string. */
export function parseKeepingLiterals(text: string): unknown {
  let out = "";
  let inString = false;
  for (let i = 0; i < text.length; i++) {
    const ch = text[i]!;
    if (inString) {
      out += ch;
      if (ch === "\\") out += text[++i] ?? "";
      else if (ch === '"') inString = false;
      continue;
    }
    if (ch === '"') {
      inString = true;
      out += ch;
      continue;
    }
    if (ch === "-" || (ch >= "0" && ch <= "9")) {
      let j = i + 1;
      while (j < text.length && /[0-9.eE+-]/.test(text[j]!)) j++;
      out += `"${text.slice(i, j)}"`;
      i = j - 1;
      continue;
    }
    out += ch;
  }
  return JSON.parse(out);
}
export const readCert = async (name: string) => parseKeepingLiterals(await Bun.file(`${dir}/${name}`).text());

// constraint_slacks names -> check names (the same mapping as src/compare.ts)
const SLACKS_59: Record<string, string> = {
  tau_positive: "tau > 0",
  tau_below_one: "tau < 1",
  sigma_positive: "sigma > 0",
  sigma_below_one: "sigma < 1",
  beta_below_one: "beta < 1",
  c_positive: "c > 0",
  epsilon_positive: "epsilon > 0",
  delta_positive: "delta > 0",
  delta_below_one_eighth: "delta < 1/8",
  kappa_positive: "kappa > 0",
  lambda_above_tau: "tau < lambda",
  lambda_above_sigma: "sigma < lambda",
  lambda_below_one: "lambda < 1",
  lambda_prime_above_lambda: "lambda < lambda'",
  lambda_prime_below_one: "lambda' < 1",
  packed_overhead: "tau(1+c/beta) < lambda",
  leaf_cost: "sigma + beta(1-sigma) < lambda'",
  guard_width: "epsilon*C1 < 1",
  dimension_upper_bound: "epsilon < 1/3",
  prime_interval_growth: "2*epsilon < 1",
  crt_layout: "epsilon(1-tau) < 1-tau",
  gaussian_cost: "3/4 + delta + 5*epsilon/4 < 1",
  prefix_cost: "epsilon(1+c) < 1",
  scalar_cost: "epsilon + delta < 1",
  alpha_below_sqrt_p: "alpha exponent 1/4+epsilon/4 < 1/2",
  gamma_sublinear: "gamma exponent 1/2+3*epsilon/2 < 1",
  K_dominates_log_p: "epsilon*c > 0",
  K_smaller_than_ell: "epsilon*c < 1 - epsilon",
  r_superpolynomial: "1 - epsilon > 0",
};
const SLACKS_COMPACT: Record<string, string> = {
  ...Object.fromEntries(Object.entries(SLACKS_59).filter(([k]) => k !== "packed_overhead")),
  beta_positive: "beta > 0",
  packed_overhead: "chi < lambda",
  reserved_axes: "max{1-c,0} < lambda'",
};
const PARAM_SLACKS = new Set(["tau_positive", "tau_below_one", "sigma_positive", "sigma_below_one", "beta_positive", "beta_below_one", "c_positive", "epsilon_positive", "delta_positive", "kappa_positive", "lambda_below_one", "lambda_prime_below_one"]);
const PARAM_FIELDS = [["tau", "tau"], ["sigma", "sigma"], ["beta", "beta"], ["epsilon", "epsilon"], ["delta", "delta"], ["C1", "C1"], ["c", "c"], ["lam", "lambda"], ["lamp", "lambdaPrime"], ["kappa", "kappa"]] as const;

/** A 2^-59-type witness block: parameters, margins, minimum, gap, limiting margins, the slacks. */
function witness59(C: Comparator, pre: string, p: Params) {
  const P = p as unknown as Record<string, Q>;
  for (const [cert, ts] of PARAM_FIELDS) C.input(`${pre}.parameters.${cert}`, P[ts]);
  const mg = margins59(p);
  const G = minimumMargin(p);
  for (const [k, gk] of Object.entries(mg)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.margins.${k}`, gk);
  C.recomputed(`${pre}.minimum_margin`, G);
  C.recomputed(`${pre}.absorption_gap`, sub(G, p.kappa));
  C.recomputed(`${pre}.limiting_margins`, Object.entries(mg).filter(([, gk]) => eq(gk, G)).map(([k]) => k).join(","));
  const byName = new Map(parameterChecks(p).map((k) => [k.name, slack(k)]));
  for (const [cert, ts] of Object.entries(SLACKS_59)) (PARAM_SLACKS.has(cert) ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.constraint_slacks.${cert}`, byName.get(ts)!);
  C.input(`${pre}.constraint_slacks.beta_positive`, p.beta);
}

/** A compact-control witness block (PR 3 "witness", PR 4 "main"). */
function witnessCompact(C: Comparator, pre: string, p: CompactParams, mg: Record<string, Q>, G: Q, recurrence: string, x: { chi: Q; leaf: Q; layer: Q; reserve: Q }) {
  const P = p as unknown as Record<string, Q>;
  for (const [cert, ts] of PARAM_FIELDS) C.input(`${pre}.parameters.${cert}`, P[ts]);
  for (const [k, gk] of Object.entries(mg)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.margins.${k}`, gk);
  C.recomputed(`${pre}.minimum_margin`, G);
  C.recomputed(`${pre}.absorption_gap`, sub(G, p.kappa));
  const byName = new Map(compactParameterChecks(p).map((k) => [k.name, slack(k)]));
  for (const [cert, ts] of Object.entries(SLACKS_COMPACT)) {
    const s = byName.get(ts);
    if (!s) throw new Error(`no check named ${ts}`);
    (PARAM_SLACKS.has(cert) ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.constraint_slacks.${cert}`, s);
  }
  C.recomputed(`${recurrence}.internal`, x.chi);
  C.recomputed(`${recurrence}.leaf`, x.leaf);
  C.recomputed(`${recurrence}.layer`, x.layer);
  C.input(`${recurrence}.preprocessing`, x.reserve); // max{1 - c, 0} of the input c
}

/** The fast-Gaussian system (PRs 5 and 6): compact slacks without the dropped conditions, new Gaussian row. */
const SLACKS_FAST: Record<string, string> = {
  ...Object.fromEntries(Object.entries(SLACKS_COMPACT).filter(([k]) => !["dimension_upper_bound", "alpha_below_sqrt_p", "gamma_sublinear", "gaussian_cost"].includes(k))),
  gaussian_cost: "2*epsilon + delta < 1",
  alpha_squared_theta_growth: "1 - 2 epsilon > 0 (b/d^2 grows, so alpha^2 theta_i >= 1 eventually)",
};

function witnessFast(C: Comparator, pre: string, p: CompactParams, mg: Record<string, Q>, G: Q, recurrence: string, x: { chi: Q; leaf: Q; layer: Q; reserve: Q }) {
  const P = p as unknown as Record<string, Q>;
  for (const [cert, ts] of PARAM_FIELDS) C.input(`${pre}.parameters.${cert}`, P[ts]);
  for (const [k, gk] of Object.entries(mg)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.margins.${k}`, gk);
  C.recomputed(`${pre}.minimum_margin`, G);
  C.recomputed(`${pre}.absorption_gap`, sub(G, p.kappa));
  C.recomputed(`${pre}.limiting_margins`, Object.entries(mg).filter(([, gk]) => eq(gk, G)).map(([k]) => k).join(","));
  const byName = new Map(fastParameterChecks(p).map((k) => [k.name, slack(k)]));
  for (const [cert, ts] of Object.entries(SLACKS_FAST)) {
    const sl = byName.get(ts);
    if (!sl) throw new Error(`no check named ${ts}`);
    (PARAM_SLACKS.has(cert) ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.constraint_slacks.${cert}`, sl);
  }
  C.recomputed(`${recurrence}.internal`, x.chi);
  C.recomputed(`${recurrence}.leaf`, x.leaf);
  C.recomputed(`${recurrence}.layer`, x.layer);
  C.input(`${recurrence}.preprocessing`, x.reserve);
}

const skip = (C: Comparator, fields: string[], why = "descriptive label") => fields.forEach((f) => C.skip(f, why));
const certQ = (C: Comparator, f: string) => parseQ(String(C.get(f)));

export async function comparePR1(print = true, cert?: unknown) {
  const C = new Comparator("PR1 paired-tuned-parameters.json", cert ?? (await readCert("pr1-paired-tuned-parameters.json")));
  const r = pr1().values;
  const p = r.params;
  skip(C, ["author", "base_commit", "base_repository", "scope", "status"]);
  C.input("bit_saving", p.a);
  C.input("complex_saving", p.ac);
  C.input("log_m_upper", q(11737n, 1000n));
  const Gold = minimumMargin(noteParams());
  C.input("comparison.previous_headline", twoPow(-59));
  C.recomputed("comparison.previous_minimum_margin", Gold);
  C.recomputed("comparison.relative_gain_over_headline", sub(mul(p.kappa, twoPow(59)), ONE));
  C.recomputed("comparison.relative_gain_over_previous_margin", sub(div(p.kappa, Gold), ONE));
  // design target
  const dp = pr1DesignParams();
  C.input("design_target.bit_saving", dp.a);
  C.recomputed("design_target.maximum_side_roles", maxSideRoles(50, dp.a, q(11737n, 1000n)));
  skip(C, ["design_target.scope", "design_target.status"]);
  witness59(C, "design_target.witness", dp); // kappa = 2^-58, as the PR states for its target
  // supremum: a different enclosure (integer square root) of the same number
  const sup = r.supremum;
  const cz = (C.get("fixed_exponent_supremum.capacity_interval") as string[]).map(parseQ);
  const cg = (C.get("fixed_exponent_supremum.margin_interval") as string[]).map(parseQ);
  C.otherMethod("fixed_exponent_supremum.capacity_interval", le(cz[0]!, sup.z.upper) && le(sup.z.lower, cz[1]!), "the two enclosures of z_* overlap (TS: integer square root; PR: bisection)");
  C.otherMethod("fixed_exponent_supremum.margin_interval", le(cg[0]!, sup.G.upper) && le(sup.G.lower, cg[1]!), "the two enclosures of G_* overlap");
  const kf = certQ(C, "fixed_exponent_supremum.kappa_fraction_lower_bound");
  C.otherMethod("fixed_exponent_supremum.kappa_fraction_lower_bound", le(kf, div(p.kappa, sup.G.lower)) && lt(q(99999996n, 10n ** 8n), kf), "cert <= kappa/(TS lower G_*), cert > 0.99999996");
  skip(C, ["fixed_exponent_supremum.bisections", "fixed_exponent_supremum.formula", "fixed_exponent_supremum.polynomial", "fixed_exponent_supremum.scope"], "method detail or descriptive string");
  // Gaussian
  C.skip("gaussian.gamma_cutoff", "descriptive string");
  C.recomputed("gaussian.gamma_exponent", add(q(1n, 2n), mul(q(3n, 2n), p.epsilon)));
  C.recomputed("gaussian.gaussian_margin", r.margins.g5);
  // integration
  C.input("integration.actual_side_roles", 509194); // recomputed by B1 of `bun run check`
  C.recomputed("integration.sufficient_side_role_budget", maxSideRoles(50, p.a, q(11737n, 1000n)));
  skip(C, ["integration.all_parameter_slacks_and_margins_match", "integration.paired_circuit_rechecked", "integration.scope", "integration.upstream_commit", "integration.verifier_models"], "Python-internal flag or label");
  // guard
  const g = ground(50);
  C.recomputed("stopped_guard.B", r.guard.B);
  C.recomputed("stopped_guard.C0", r.guard.C0);
  C.recomputed("stopped_guard.E", r.guard.E);
  C.input("stopped_guard.C1", p.C1);
  C.input("stopped_guard.beta", p.beta);
  C.input("stopped_guard.h", 50);
  C.recomputed("stopped_guard.m", g.m);
  C.recomputed("stopped_guard.complex_s", r.complex.s);
  C.recomputed("stopped_guard.one_piece_depth_exponent", sub(q(5n), mul(q(4n), p.beta)));
  C.recomputed("stopped_guard.depth_with_piece_count_exponent", add(sub(q(5n), mul(q(4n), p.beta)), q(1n, 2n)));
  C.recomputed("stopped_guard.s_below_m_fifth", r.complex.s < g.m ** 5n);
  witness59(C, "witness", p);
  return C.finish(print);
}

export async function comparePR2(print = true, cert?: unknown) {
  const C = new Comparator("PR2 aligned-paired-network.json", cert ?? (await readCert("pr2-aligned-paired-network.json")));
  const r = pr2().values;
  const p = r.params;
  const g = ground(50);
  const A = r.aligned;
  const bp = r.bit;
  for (const [f, v] of [["D", bp.deficit], ["L", bp.L], ["N", g.N], ["W", bp.W], ["eta", bp.eta], ["m", g.m], ["s", bp.s], ["v", g.v], ["side_roles_per_invocation", BigInt(A.report.roles)]] as const) C.recomputed(`bit_counts.${f}`, v);
  C.input("bit_counts.h", 50);
  C.recomputed("bit_deficit_slack", sub(bp.eta, mul(p.a, q(11737n, 1000n))));
  C.input("bit_saving", p.a);
  const cx = complexNetwork(50);
  for (const [f, v] of [["Lc", cx.L], ["N", g.N], ["Wc", cx.W], ["eta_c", cx.eta], ["m", g.m], ["sc", cx.s], ["v", g.v]] as const) C.recomputed(`complex_counts.${f}`, v);
  C.input("complex_counts.h", 50);
  C.recomputed("complex_deficit_slack", sub(cx.eta, mul(p.ac, q(11737n, 1000n))));
  C.input("complex_saving", p.ac);
  C.recomputed("fixed_network_ceiling.value", r.ceiling.value);
  C.recomputed("fixed_network_ceiling.strictly_below_2_to_minus_58", lt(r.ceiling.value, twoPow(-58)));
  C.skip("fixed_network_ceiling.scope", "descriptive string");
  const support = A.report.allAdditionsDisjoint && A.report.everyNodeHasCommonPoint && A.report.allPartialOutputsExact && A.report.everyNodeUsed;
  const certTrue = (f: string) => String(C.get(f)) === "true";
  C.otherMethod("frames.forward_frames_nested", support && certTrue("frames.forward_frames_nested"), "support-level argument (Python: per compiled role)");
  C.otherMethod("frames.reverse_complement_frames_nested", support && certTrue("frames.reverse_complement_frames_nested"), "support-level argument (Python: per compiled role)");
  C.skip("frames.nondegeneracy", "descriptive string");
  C.recomputed("frames.roles", A.report.roles);
  C.skip("gaussian.alpha_definition", "descriptive string");
  C.skip("gaussian.gamma_cutoff", "descriptive string");
  C.recomputed("gaussian.alpha_exponent", add(q(1n, 4n), mul(q(1n, 4n), p.epsilon)));
  C.recomputed("gaussian.gamma_exponent", add(q(1n, 2n), mul(q(3n, 2n), p.epsilon)));
  C.recomputed("global_circuit.additions", A.report.additions);
  C.recomputed("global_circuit.merged_additions", A.report.mergedAdditions);
  C.recomputed("global_circuit.all_additions_disjoint", A.report.allAdditionsDisjoint);
  C.recomputed("global_circuit.all_partial_outputs_exact", A.report.allPartialOutputsExact);
  C.recomputed("global_circuit.every_node_has_common_point", A.report.everyNodeHasCommonPoint);
  C.recomputed("global_circuit.roles", A.report.roles);
  C.input("global_circuit.h", 50);
  C.input("global_circuit.inputs", Number(g.v));
  C.input("global_circuit.partial_outputs", A.report.partialOutputs);
  C.skip("global_circuit.circuit_sha256", "hash of the Python encoding of node ids");
  const L = A.localReport;
  C.recomputed("local_circuit.additions", L.additions);
  C.recomputed("local_circuit.all_additions_disjoint", L.allAdditionsDisjoint);
  C.recomputed("local_circuit.all_output_supports_exact", L.allOutputSupportsExact);
  C.skip("local_circuit.circuit_sha256", "hash of the Python encoding of node ids");
  C.input("local_circuit.inputs", L.outputs);
  C.input("local_circuit.n", L.n);
  C.recomputed("local_circuit.nonzero_coefficients", L.nonzeroCoefficients);
  C.input("local_circuit.outputs", L.outputs);
  C.recomputed("local_circuit.scratch_roles", L.additions + L.outputs);
  C.recomputed("log_enclosure.0", r.logm.lower);
  C.recomputed("log_enclosure.1", r.logm.upper);
  C.input("log_m_upper", q(11737n, 1000n));
  skip(C, ["point_order_rule", "scope", "status", "upstream_commit"]);
  C.recomputed("stopped_guard.B", r.guard.B);
  C.recomputed("stopped_guard.C0", r.guard.C0);
  C.recomputed("stopped_guard.E", r.guard.E);
  C.input("stopped_guard.C1", p.C1);
  C.input("stopped_guard.beta", p.beta);
  C.input("stopped_guard.h", 50);
  C.recomputed("stopped_guard.m", g.m);
  C.recomputed("stopped_guard.complex_s", cx.s);
  C.recomputed("stopped_guard.one_piece_depth_exponent", sub(q(5n), mul(q(4n), p.beta)));
  C.recomputed("stopped_guard.depth_with_piece_count_exponent", add(sub(q(5n), mul(q(4n), p.beta)), q(1n, 2n)));
  C.recomputed("stopped_guard.s_below_m_fifth", cx.s < g.m ** 5n);
  C.skip("stopped_guard.scope", "descriptive string");
  witness59(C, "witness", p);
  C.recomputed("witness.all_margins_at_least_twice_kappa", le(mul(q(2n), p.kappa), r.G));
  skip(C, ["witness.assembly_model", "witness.generalized_beta", "witness.guard_model", "witness.slack_rule"]);
  return C.finish(print);
}

export async function comparePR3(print = true, cert?: unknown) {
  const C = new Comparator("PR3 complex-network.json", cert ?? (await readCert("pr3-complex-network.json")));
  const r = pr3().values;
  const p = r.params;
  const c = r.circuit;
  const nw = r.network;
  const g = ground(25);
  C.input("bit_saving", p.a);
  C.input("complex_saving", p.ac);
  C.recomputed("circuit.additions", c.additions);
  C.recomputed("circuit.disjoint_additions", c.disjointAdditions);
  C.recomputed("circuit.pair_star_additions", c.starAdditions);
  C.recomputed("circuit.injections", c.injections);
  C.recomputed("circuit.roles", c.additions + c.injections);
  C.input("circuit.h", 25);
  C.recomputed("circuit.v", g.v);
  // a decimal in the certificate: R / v to three decimals (truncated here; compared as text)
  C.recomputed("circuit.roles_per_target", toDecimal(div(q(BigInt(c.additions + c.injections)), q(g.v)), 3));
  C.recomputed("complex_counts.I", 3n * g.v * g.v);
  C.recomputed("complex_counts.L", nw.L);
  C.recomputed("complex_counts.N", nw.N);
  C.recomputed("complex_counts.W", nw.W);
  C.input("complex_counts.central_roles", 26); // h + 1
  C.recomputed("complex_counts.deficit", nw.deficit);
  C.recomputed("complex_counts.eta", nw.eta);
  C.input("complex_counts.h", 25);
  C.recomputed("complex_counts.m", nw.m);
  C.recomputed("complex_counts.original_side_wires_per_invocation", BigInt(c.nonzeroCoefficients));
  C.recomputed("complex_counts.s", nw.s);
  C.recomputed("complex_counts.side_roles_per_invocation", c.additions + c.injections);
  C.recomputed("complex_counts.v", g.v);
  C.recomputed("complex_deficit_slack", sub(nw.eta, mul(p.ac, q(966n, 100n))));
  C.recomputed("gates.gates_per_invocation", r.gatesPerInvocation);
  C.recomputed("gates.total_gates", r.gates);
  C.recomputed("gates.twelve_W", 12n * nw.W);
  C.recomputed("improvement_over_compact_control", div(p.kappa, q(83n, 10n ** 12n)));
  C.recomputed("labels.active_nodes", c.inputsUsed + c.additions);
  C.recomputed("labels.checked_inclusions", 2 * c.additions + c.injections);
  skip(C, ["labels.all_labels_nondegenerate", "labels.all_residuals_have_odd_vectors"], "binary label algebra: circuit validity, not checked here");
  const le_ = (C.get("log_enclosure") as string[]).map(parseQ);
  C.otherMethod("log_enclosure", le(le_[0]!, r.logm.upper) && le(r.logm.lower, le_[1]!) && lt(le_[1]!, q(966n, 100n)), "the enclosures of log 15625 overlap; both below 966/100");
  C.input("log_m_upper", q(966n, 100n));
  skip(C, ["role_frames.forward_frames_nested", "role_frames.reverse_complement_frames_nested"], "per-role frame check: circuit validity, not checked here");
  C.recomputed("role_frames.roles", c.additions + c.injections);
  skip(C, ["scope", "status", "upstream_commit", "scoped_ceiling.scope"]);
  C.recomputed("scoped_ceiling.upper", div(p.a, q(5n)));
  C.recomputed("scoped_ceiling.below_2_to_minus_30", lt(div(p.a, q(5n)), twoPow(-30)));
  C.skip("side_map.coefficients", "descriptive string");
  C.recomputed("side_map.nonzero_coefficients", c.nonzeroCoefficients);
  C.recomputed("side_map.side_map_exact", c.sideMapExact);
  C.recomputed("side_map.targets", g.v);
  witnessCompact(C, "witness", p, r.margins, r.G, "witness.recurrence", r.exponents);
  C.recomputed("witness.limiting_margins", Object.entries(r.margins).filter(([, gk]) => eq(gk, r.G)).map(([k]) => k).join(","));
  C.recomputed("witness.guard.B", r.guard.B);
  C.recomputed("witness.guard.C0", r.guard.C0);
  C.recomputed("witness.guard.E", r.guard.E);
  C.input("witness.guard.C1", p.C1);
  C.input("witness.guard.beta", p.beta);
  C.input("witness.guard.zeta", p.zeta);
  C.recomputed("witness.guard.m", nw.m);
  C.recomputed("witness.guard.s", nw.s);
  return C.finish(print);
}

export async function comparePR4(print = true, cert?: unknown) {
  const C = new Comparator("PR4 retained-complex-layer.json", cert ?? (await readCert("pr4-retained-complex-layer.json")));
  const r = pr4().values;
  const p = r.params;
  const nw = r.network;
  const d = r.retained.disjoint;
  skip(C, ["frames.both_physical_frame_directions", "frames.pivot_and_fanout_roles_distinct"], "frame check: circuit validity, not checked here");
  C.recomputed("frames.roles", nw.Raux);
  C.input("kappa", p.kappa);
  witnessCompact(C, "main", p, r.margins, r.G, "main.exponents", r.exponents);
  for (const [f, v] of [["D", nw.deficit], ["L", nw.L], ["N", nw.N], ["W", nw.W], ["additions", nw.C], ["eta", nw.eta], ["m", nw.m], ["roles", nw.Raux], ["s", nw.s], ["v", nw.v]] as const) C.recomputed(`main.counts.${f}`, v);
  C.recomputed("main.counts.side_outputs", nw.q - 24n);
  C.input("main.counts.h", 24);
  C.input("main.counts.retained_totals", 24);
  C.recomputed("main.deficit_slack", sub(nw.eta, mul(p.ac, q(477n, 50n))));
  C.recomputed("main.guard.B", r.guard.B);
  C.recomputed("main.guard.C0", r.guard.C0);
  C.recomputed("main.guard.E", r.guard.E);
  C.input("main.guard.C1", p.C1);
  C.input("main.guard.zeta", p.zeta);
  C.input("main.guard.scalar_gates", 6696869422848n); // stated in the note; only "< 12 W" is checked
  const li = (C.get("main.log_interval") as string[]).map(parseQ);
  C.otherMethod("main.log_interval", le(li[0]!, r.logm.upper) && le(r.logm.lower, li[1]!) && lt(li[1]!, q(477n, 50n)), "the enclosures of log 13824 overlap; both below 477/50");
  C.input("main.log_upper", q(477n, 50n));
  C.recomputed("producer.additions", nw.C);
  C.input("producer.h", 24);
  C.recomputed("producer.inputs", nw.v);
  C.recomputed("producer.output_residual_checks", nw.q - 24n);
  C.recomputed("producer.partial_outputs", nw.q - 24n);
  C.input("producer.retained_totals", 24);
  C.recomputed("producer.roles", nw.Raux);
  C.recomputed("producer.two_output_uses", nw.q2);
  C.recomputed("producer.zero_output_uses", d.outputs);
  skip(C, ["producer.activation_and_retirement_checked", "producer.all_residuals_nonalt", "producer.exact_total_multiplicities", "producer.full_coefficient_map_exact"], "circuit validity, not checked here");
  C.skip("producer.circuit_sha256", "hash of the Python encoding");
  // proof hashes: file integrity at the PR head, not mathematics
  for (const f of Object.keys(C.get("proof_sha256") as object)) {
    if (!CLONE) {
      C.skip(`proof_sha256.${f}`, "set PR_CLONE to a clone containing commit 42a88ef to recompute");
      continue;
    }
    const blob = Bun.spawnSync(["git", "-C", CLONE, "show", `42a88ef0682e078e63df52e7a9ea3c53d568a469:${f}`]).stdout;
    C.recomputed(`proof_sha256.${f}`, createHash("sha256").update(blob).digest("hex"));
  }
  C.recomputed("ratio_over_compact_witness", div(p.kappa, q(83n, 10n ** 12n)));
  skip(C, ["scope", "status", "upstream_commit"]);
  return C.finish(print);
}

export async function comparePR4b(print = true, cert?: unknown) {
  const C = new Comparator("PR4b retained-complex-layer.json (head 8c225e6)", cert ?? (await readCert("pr4b-retained-complex-layer.json")));
  const r = pr4b().values;
  const p = r.params;
  const nw = r.network;
  const ci = r.circuit;
  skip(C, ["frames.both_physical_frame_directions", "frames.pivot_and_fanout_roles_distinct"], "frame check: circuit validity, not checked here");
  C.recomputed("frames.roles", r.R);
  skip(C, ["imported_builder.author", "imported_builder.commit", "imported_builder.pr"], "attribution");
  C.input("kappa", p.kappa);
  witnessCompact(C, "main", p, r.margins, r.G, "main.exponents", r.exponents);
  for (const [f, v] of [["D", nw.D], ["L", nw.L], ["N", nw.N], ["W", nw.W], ["additions", r.C], ["eta", nw.eta], ["m", nw.m], ["roles", r.R], ["s", nw.s], ["v", nw.v]] as const) C.recomputed(`main.counts.${f}`, v);
  C.recomputed("main.counts.base_additions", ci.base.additions);
  C.recomputed("main.counts.new_ancestors", ci.newAncestors);
  C.recomputed("main.counts.side_outputs", ci.base.injections);
  C.input("main.counts.h", 24);
  C.recomputed("main.counts.retained_totals", ci.totals.length);
  C.recomputed("main.deficit_slack", sub(nw.eta, mul(p.ac, q(477n, 50n))));
  C.recomputed("main.guard.B", r.guard.B);
  C.recomputed("main.guard.C0", r.guard.C0);
  C.recomputed("main.guard.E", r.guard.E);
  C.input("main.guard.C1", p.C1);
  C.input("main.guard.zeta", p.zeta);
  C.recomputed("main.guard.scalar_gates", r.gates);
  const li = (C.get("main.log_interval") as string[]).map(parseQ);
  C.otherMethod("main.log_interval", le(li[0]!, r.logm.upper) && le(r.logm.lower, li[1]!) && lt(li[1]!, q(477n, 50n)), "the enclosures of log 13824 overlap; both below 477/50");
  C.input("main.log_upper", q(477n, 50n));
  C.recomputed("producer.additions", r.C);
  C.input("producer.h", 24);
  C.recomputed("producer.inputs", nw.v);
  C.recomputed("producer.output_residual_checks", ci.base.injections);
  C.recomputed("producer.partial_outputs", ci.base.injections);
  C.recomputed("producer.retained_totals", ci.totals.length);
  C.recomputed("producer.roles", r.R);
  C.recomputed("producer.two_output_uses", ci.minus);
  C.recomputed("producer.zero_output_uses", ci.plus);
  C.recomputed("producer.exact_total_multiplicities", ci.totalsExact && ci.disjoint);
  C.recomputed("producer.full_coefficient_map_exact", ci.base.sideMapExact);
  skip(C, ["producer.activation_and_retirement_checked", "producer.all_residuals_nonalt"], "label algebra: circuit validity, not checked here");
  C.skip("producer.circuit_sha256", "hash of the Python encoding");
  for (const f of Object.keys(C.get("proof_sha256") as object)) {
    if (!CLONE) {
      C.skip(`proof_sha256.${f}`, "set PR_CLONE to a clone containing commit 8c225e6 to recompute");
      continue;
    }
    const blob = Bun.spawnSync(["git", "-C", CLONE, "show", `8c225e619168c0141dcfcba3b68a65bbed6a8729:${f}`]).stdout;
    C.recomputed(`proof_sha256.${f}`, createHash("sha256").update(blob).digest("hex"));
  }
  C.recomputed("ratio_over_compact_witness", div(p.kappa, q(83n, 10n ** 12n)));
  skip(C, ["scope", "status", "upstream_commit"]);
  return C.finish(print);
}

export async function comparePR5(print = true, cert?: unknown) {
  const C = new Comparator("PR5 fast-gaussian.json", cert ?? (await readCert("pr5-fast-gaussian.json")));
  const r = pr5().values;
  const p = r.params;
  const nw = r.network;
  C.input("bit_saving", p.a);
  C.input("complex_saving", p.ac);
  C.recomputed("complex_counts.W", nw.W);
  C.recomputed("complex_counts.eta", nw.eta);
  C.input("complex_counts.h", 25);
  C.recomputed("complex_counts.s", nw.s);
  C.skip("gaussian_cost_power", "descriptive string (the row is checked in PR5-B as g5 = 1 - delta - 2 eps)");
  C.recomputed("improvement_over_compact_control", div(p.kappa, q(83n, 10n ** 12n)));
  C.recomputed("improvement_over_compressed_complex", div(p.kappa, q(59n, 10n ** 11n)));
  const samples = C.get("neumann_samples") as Record<string, string>[];
  samples.forEach((smp, i) => {
    const b = BigInt(smp.b!);
    const d = BigInt(smp.d!);
    const w = fastWidthInstance(b, d);
    C.input(`neumann_samples.${i}.b`, b);
    C.input(`neumann_samples.${i}.d`, d);
    C.recomputed(`neumann_samples.${i}.alpha`, w.alpha, true);
    C.recomputed(`neumann_samples.${i}.gamma`, w.gamma, true);
    C.recomputed(`neumann_samples.${i}.n_new`, w.nMax, true);
    C.recomputed(`neumann_samples.${i}.n_hvdh`, w.nHvdh, true);
    C.recomputed(`neumann_samples.${i}.n`, w.nMax < w.nHvdh ? w.nMax : w.nHvdh, true);
  });
  skip(C, ["scope", "status", "upstream_commit", "scoped_ceiling.scope"]);
  C.recomputed("scoped_ceiling.upper", div(p.a, q(2n)));
  C.recomputed("scoped_ceiling.below_2_to_minus_29", lt(div(p.a, q(2n)), twoPow(-29)));
  for (const key of Object.keys(C.get("step_inequality_minimum_excess") as object)) {
    const [s_, t_] = key.split("/").map(Number);
    const e = stepExcess(s_!, t_!, Math.min(3 * s_!, 120));
    C.recomputed(`step_inequality_minimum_excess.${key}`, e.min, true);
  }
  witnessFast(C, "witness", p, r.margins, r.G, "witness.recurrence", r.exponents);
  C.recomputed("witness.guard.B", r.guard.B);
  C.recomputed("witness.guard.C0", r.guard.C0);
  C.recomputed("witness.guard.E", r.guard.E);
  C.input("witness.guard.C1", p.C1);
  C.input("witness.guard.beta", p.beta);
  C.input("witness.guard.zeta", p.zeta);
  C.recomputed("witness.guard.m", nw.m);
  C.recomputed("witness.guard.s", nw.s);
  return C.finish(print);
}

export async function comparePR6(print = true, cert?: unknown) {
  const C = new Comparator("PR6 aligned-bit-network.json", cert ?? (await readCert("pr6-aligned-bit-network.json")));
  const r = pr6().values;
  const p = r.params;
  const nw = r.network;
  const rep = r.aligned.report;
  const g = ground(50);
  for (const [f, v] of [["L", nw.L], ["N", nw.N], ["W", nw.W], ["deficit", nw.D], ["eta", nw.eta], ["m", nw.m], ["s", nw.s], ["v", nw.v], ["side_and_center_roles", r.R]] as const) C.recomputed(`bit_counts.${f}`, v);
  C.input("bit_counts.h", 50);
  C.input("bit_counts.published_roles", 509244n); // 509194 recomputed by B1 of `bun run check`, plus h
  C.recomputed("bit_deficit_slack", sub(nw.eta, mul(p.a, q(11737n, 1000n))));
  C.input("bit_saving", p.a);
  C.recomputed("circuit.additions", rep.additions);
  C.recomputed("circuit.all_additions_disjoint", rep.allAdditionsDisjoint && rep.totalsDisjoint);
  C.recomputed("circuit.all_outputs_exact", rep.allPartialOutputsExact);
  C.recomputed("circuit.centers", rep.totalsCount);
  C.skip("circuit.circuit_sha256", "hash of the Python encoding of node ids");
  C.recomputed("circuit.every_node_has_common_point", rep.everyNodeHasCommonPoint);
  C.input("circuit.h", 50);
  C.input("circuit.inputs", Number(g.v));
  C.recomputed("circuit.roles", r.R);
  C.recomputed("circuit.side_outputs", rep.partialOutputs);
  C.recomputed("circuit.totals_exact", rep.totalsExact);
  C.input("complex_saving", p.ac);
  skip(C, ["frames.forward_frames_nested", "frames.reverse_complement_frames_nested"], "per-role frames including the new center frames D_{H_i}: written argument, not checked here");
  C.skip("frames.nondegeneracy", "descriptive string");
  C.recomputed("frames.roles", r.R);
  C.recomputed("improvement_over_fast_gaussian", div(p.kappa, q(1479n, 10n ** 12n)));
  const le_ = (C.get("log_enclosure") as string[]).map(parseQ);
  C.otherMethod("log_enclosure", le(le_[0]!, r.logm.upper) && le(r.logm.lower, le_[1]!) && lt(le_[1]!, q(11737n, 1000n)), "the enclosures of log 125000 overlap; both below 11737/1000");
  C.input("log_m_upper", q(11737n, 1000n));
  C.input("previous_bit_saving", q(296n, 10n ** 11n));
  C.recomputed("previous_counts.deficit", g.N - 6n * g.v * g.v * 2500n);
  C.input("previous_counts.roles", 509244n);
  skip(C, ["scope", "status", "upstream_commit", "scoped_ceiling.scope"]);
  C.recomputed("scoped_ceiling.upper", div(p.a, q(2n)));
  C.recomputed("scoped_ceiling.below_2_to_minus_29", lt(div(p.a, q(2n)), twoPow(-29)));
  witnessFast(C, "witness", p, r.margins, r.G, "witness.recurrence", r.exponents);
  C.recomputed("witness.guard.B", r.guard.B);
  C.recomputed("witness.guard.C0", r.guard.C0);
  C.recomputed("witness.guard.E", r.guard.E);
  C.input("witness.guard.C1", p.C1);
  C.input("witness.guard.beta", p.beta);
  C.input("witness.guard.zeta", p.zeta);
  C.recomputed("witness.guard.m", r.complex.m);
  C.recomputed("witness.guard.s", r.complex.s);
  return C.finish(print);
}

/** A file of the PR head, hashed (PR_CLONE only). */
function cloneHash(C: Comparator, field: string, commit: string, path: string) {
  if (!CLONE) {
    C.skip(field, `set PR_CLONE to a clone containing commit ${commit.slice(0, 7)} to recompute`);
    return;
  }
  const r = Bun.spawnSync(["git", "-C", CLONE, "show", `${commit}:${path}`]);
  if (r.exitCode !== 0) {
    C.skip(field, `commit ${commit.slice(0, 7)} not in PR_CLONE`);
    return;
  }
  C.recomputed(field, createHash("sha256").update(r.stdout).digest("hex"));
}

const PR7_HEAD = "6725c6a17b17871a35353fd29157f4ed851bc114";
const PR8_HEAD = "9454645ccb61663d13dcf7cc69ade762665ae9ed";
const BASE = "6e564879f51ae16f23d392e9e196c605f36d90df";

export async function comparePR7(print = true, cert?: unknown) {
  const C = new Comparator("PR7 prime-field28.json", cert ?? (await readCert("pr7-prime-field28.json")));
  const r = pr7().values;
  const p = r.params;
  const cc = r.complexCircuit;
  const cn = r.complex;
  const bn = r.bit;
  const G = r.global;
  const loc = r.local;
  // complex circuit (rebuilt at h = 28)
  C.recomputed("complex_checks.labels.active_nodes", cc.inputsUsed + cc.additions);
  C.recomputed("complex_checks.labels.checked_inclusions", 2 * cc.additions + cc.injections);
  skip(C, ["complex_checks.labels.all_labels_nondegenerate", "complex_checks.labels.all_residuals_have_odd_vectors"], "binary label algebra: circuit validity, not checked here");
  C.skip("complex_checks.map.coefficients", "descriptive string");
  C.recomputed("complex_checks.map.nonzero_coefficients", cc.nonzeroCoefficients);
  C.recomputed("complex_checks.map.side_map_exact", cc.sideMapExact);
  C.recomputed("complex_checks.map.targets", Number(cn.v));
  skip(C, ["complex_checks.roles.forward_frames_nested", "complex_checks.roles.reverse_complement_frames_nested"], "per-role frame check: circuit validity, not checked here");
  C.recomputed("complex_checks.roles.roles", cc.additions + cc.injections);
  C.recomputed("complex_checks.stats.additions", cc.additions);
  C.recomputed("complex_checks.stats.disjoint_additions", cc.disjointAdditions);
  C.input("complex_checks.stats.h", 28);
  C.recomputed("complex_checks.stats.injections", cc.injections);
  C.recomputed("complex_checks.stats.pair_star_additions", cc.starAdditions);
  C.recomputed("complex_checks.stats.roles", cc.additions + cc.injections);
  C.recomputed("complex_checks.stats.roles_per_target", toDecimal(div(q(BigInt(cc.additions + cc.injections)), q(cn.v)), 3));
  C.recomputed("complex_checks.stats.v", Number(cn.v));
  // matching
  C.recomputed("matching.distinct_images", r.matching.distinct);
  C.recomputed("matching.domain", r.matching.domain);
  C.recomputed("matching.every_intersection_two", r.matching.allTwo);
  C.input("matching.h", 28);
  // global producer before replacement
  const gb = "producer.global_before_replacement";
  C.recomputed(`${gb}.all_inputs_active`, G.inputsActive === G.v);
  C.skip(`${gb}.exact_support_keys`, "property of the PR's C++ keys (the TS keys are exact bit sets too)");
  C.input(`${gb}.h`, 28);
  C.recomputed(`${gb}.local_inputs`, Number(binom(26, 3)));
  C.recomputed(`${gb}.outputs`, G.roots);
  C.recomputed(`${gb}.pruned_additions`, G.active);
  C.recomputed(`${gb}.removed_after_merging`, G.removed);
  C.recomputed(`${gb}.roles`, G.active + G.roots);
  C.recomputed(`${gb}.topological_order_checked`, G.topological);
  C.recomputed(`${gb}.unique_additions`, G.unique);
  const it = "producer.independent_template_check";
  C.recomputed(`${it}.every_boundary_sum_verified`, G.templatesValid);
  C.recomputed(`${it}.every_template_addition_disjoint`, G.templatesValid);
  C.recomputed(`${it}.new_star_additions`, G.newStar);
  C.recomputed(`${it}.old_star_additions`, G.oldStar);
  C.recomputed(`${it}.optimized_additions`, G.c);
  C.recomputed(`${it}.optimized_stars`, G.starsRequested);
  C.recomputed(`${it}.role_upper_bound`, G.c + G.roots);
  C.recomputed(`${it}.verified_templates`, G.templates);
  // local producer
  C.recomputed("producer.local.additions", loc.additions);
  for (const k of ["0", "1", "2"]) C.recomputed(`producer.local.additions_by_core.${k}`, loc.byCore[Number(k)] ?? 0);
  C.recomputed("producer.local.all_disjoint_output_coefficients_exact", loc.outputsExact && loc.allDisjoint);
  C.input("producer.local.base", 4);
  C.skip("producer.local.binary_sha256", "hash of the Python's binary export");
  C.recomputed("producer.local.inputs", loc.inputs);
  C.input("producer.local.n", 26);
  C.recomputed("producer.local.outputs", loc.outputs);
  C.recomputed("producer.local.retained_additions", loc.retainedAdditions);
  C.recomputed("producer.local.retained_total_exact", loc.totalExact);
  C.recomputed("producer.local.roles", loc.additions + loc.outputs);
  {
    const cv = parseQ(String(C.get("producer.local.roles_per_output")).replace(/^(\d+)\.(\d+)$/, (_, a, b) => `${a}${b}/1${"0".repeat(b.length)}`));
    const exact = q(BigInt(loc.additions + loc.outputs), BigInt(loc.outputs));
    const d = sub(cv, exact);
    C.otherMethod("producer.local.roles_per_output", lt(d.num < 0n ? q(-d.num, d.den) : d, q(1n, 10n ** 13n)), `float within 1e-13 of ${show(exact)}`);
  }
  C.skip("producer.local.status", "descriptive string");
  C.recomputed("producer.replacements.new_additions", G.newStar);
  C.recomputed("producer.replacements.old_additions", G.oldStar);
  C.recomputed("producer.replacements.saved", G.oldStar - G.newStar);
  C.skip("producer.replacements.sha256", "hash of the Python's template export");
  C.recomputed("producer.replacements.stars", G.starsRequested);
  C.recomputed("producer.replacements.templates", G.templates);
  // proof hashes (file integrity at the PR head)
  for (const f of Object.keys(C.get("proof_sha256") as object)) cloneHash(C, `proof_sha256.${f}`, PR7_HEAD, f);
  skip(C, ["scope", "status", "upstream_commit"]);
  // small controls at h = 8: the coefficient count is rebuilt here; the scalar and frame simulations are not
  const g8 = mergeProducers(8, buildPairedTriple(6, true).graph);
  const p8 = prune(g8);
  skip(C, ["small_controls.all_dirty_basis.corrected_three_stage_exchange", "small_controls.all_dirty_basis.dirty_scratch_restored", "small_controls.all_dirty_basis.forward_inverse_exact"], "scalar simulation at h = 8: circuit validity, not checked here");
  C.recomputed("small_controls.all_dirty_basis.all_basis_inputs", p8.additions + g8.roots.length + 2 * g8.v); // auxiliary roles plus the X and Y banks
  C.input("small_controls.all_dirty_basis.h", 8);
  C.skip("small_controls.coefficients.every_node_has_common_pair", "true by construction of the contexts (every node of context C contains C)");
  C.input("small_controls.coefficients.h", 8);
  C.recomputed("small_controls.coefficients.inputs", g8.v);
  C.recomputed("small_controls.coefficients.roles", p8.additions + g8.roots.length);
  skip(C, ["small_controls.coefficients.retained_coefficients_exact", "small_controls.coefficients.side_coefficients_exact"], "F3 coefficient simulation at h = 8 (the h = 28 producer outputs are exact by the local check)");
  for (const i of [0, 1]) {
    C.recomputed(`small_controls.physical_frames.frames.${i}.loss`, binom(8, 2) * 6n);
    skip(C, [`small_controls.physical_frames.frames.${i}.every_edge_nested_and_nondegenerate`, `small_controls.physical_frames.frames.${i}.reverse`, `small_controls.physical_frames.frames.${i}.total_rank`], "rational frame simulation at h = 8, not checked here");
  }
  C.input("small_controls.physical_frames.h", 8);
  // the witness
  const w = "witness";
  C.recomputed(`${w}.absorption_gap`, sub(r.G, p.kappa));
  for (const [f, val] of [["D", bn.D], ["L", bn.L], ["N", bn.N], ["W", bn.W], ["eta", bn.eta], ["m", bn.m], ["roles", BigInt(G.c + G.roots)], ["s", bn.s], ["v", bn.v]] as const) C.recomputed(`${w}.bit.${f}`, val);
  C.input(`${w}.bit.h`, 28);
  C.recomputed(`${w}.bit.retained_totals`, binom(28, 2));
  for (const [f, val] of [["D", cn.D], ["I", cn.I], ["L", cn.L], ["N", cn.N], ["W", cn.W], ["eta", cn.eta], ["m", cn.m], ["roles", BigInt(cc.additions + cc.injections)], ["s", cn.s], ["scalar_gates", r.gates], ["v", cn.v]] as const) C.recomputed(`${w}.complex.${f}`, val);
  C.input(`${w}.complex.h`, 28);
  const byName = new Map(fastParameterChecks(p).map((k) => [k.name, slack(k)]));
  for (const [cert, ts] of Object.entries(SLACKS_FAST)) {
    const sl = byName.get(ts);
    if (!sl) throw new Error(`no check named ${ts}`);
    (PARAM_SLACKS.has(cert) ? C.input.bind(C) : C.recomputed.bind(C))(`${w}.constraints.${cert}`, sl);
  }
  C.recomputed(`${w}.deficit_slacks.bit`, sub(bn.eta, mul(p.a, q(9997n, 1000n))));
  C.recomputed(`${w}.deficit_slacks.complex`, sub(cn.eta, mul(p.ac, q(10n))));
  C.recomputed(`${w}.guard.B`, r.guard.B);
  C.recomputed(`${w}.guard.C0`, r.guard.C0);
  C.recomputed(`${w}.guard.E`, r.guard.E);
  C.input(`${w}.guard.C1`, p.C1);
  C.input(`${w}.guard.beta`, p.beta);
  C.input(`${w}.guard.zeta`, p.zeta);
  C.recomputed(`${w}.guard.m`, cn.m);
  C.recomputed(`${w}.guard.s`, cn.s);
  C.input(`${w}.log_upper.bit`, q(9997n, 1000n));
  C.input(`${w}.log_upper.complex`, q(10n));
  for (const [k, gk] of Object.entries(r.margins)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`${w}.margins.${k}`, gk);
  C.recomputed(`${w}.minimum_margin`, r.G);
  const P = p as unknown as Record<string, Q>;
  for (const [cf, ts] of PARAM_FIELDS.filter(([cf]) => cf !== "zeta")) C.input(`${w}.parameters.${cf}`, P[ts]);
  C.recomputed(`${w}.recurrence.internal`, r.exponents.chi);
  C.recomputed(`${w}.recurrence.layer`, r.exponents.layer);
  C.recomputed(`${w}.recurrence.leaf`, r.exponents.leaf);
  C.input(`${w}.recurrence.preprocessing`, r.exponents.reserve);
  return C.finish(print);
}

export async function comparePR8(print = true, cert?: unknown) {
  const C = new Comparator("PR8 geometric-complex certificate.json", cert ?? (await readCert("pr8-geometric-certificate.json")));
  const r = pr8().values;
  const p = r.params;
  const nw = r.network;
  const c = r.circuits;
  for (const [f, val] of [["L", nw.L], ["N", nw.N], ["W", nw.W], ["s", nw.s], ["eta", nw.eta], ["h", nw.h], ["m", nw.m], ["v", nw.v], ["side_roles", r.R]] as const) C.recomputed(f, val);
  C.input("n", 25);
  C.input("complex_saving", p.ac);
  C.recomputed("original_side_roles", 2300n * (binom(22, 3) + 66n));
  C.recomputed("improvement_factor", div(p.kappa, q(83n, 10n ** 12n)));
  // the exact deficit slack and the saving lower bound: the PR's log enclosure is not ours
  {
    const cs = parseQ(String(C.get("complex_deficit_slack")));
    const theirLogUpper = div(sub(nw.eta, cs), p.ac);
    C.otherMethod("complex_deficit_slack", cs.num > 0n && le(r.logm.lower, theirLogUpper), "positive; the implied log m upper bound lies above the TS lower enclosure");
    const sl = parseQ(String(C.get("saving_lower")));
    C.otherMethod("saving_lower", le(sl, r.enclosure.upper) && lt(p.ac, sl), "below the TS upper enclosure of the actual saving and above a_c");
  }
  for (const [key, circ, rel] of [["disjoint", c.D, "disjoint"], ["intersection_two", c.E, "intersection_two"]] as const) {
    C.recomputed(`${key}.additions`, circ.additions);
    C.recomputed(`${key}.outputs`, circ.outputs);
    C.recomputed(`${key}.roles`, circ.additions + circ.outputs);
    C.recomputed(`${key}.disjoint_addition_supports`, circ.allDisjoint);
    C.recomputed(`${key}.exact_supports`, circ.outputsExact);
    C.input(`${key}.relation`, rel);
  }
  [c.D, c.E].forEach((circ, i) => {
    const f = `full_circuits.${i}`;
    C.recomputed(`${f}.additions`, circ.additions);
    C.recomputed(`${f}.outputs`, circ.outputs);
    C.recomputed(`${f}.roles`, circ.additions + circ.outputs);
    C.recomputed(`${f}.compiled_roles`, circ.additions + circ.outputs);
    C.recomputed(`${f}.disjoint_addition_supports`, circ.allDisjoint);
    C.recomputed(`${f}.exact_supports`, circ.outputsExact);
    C.input(`${f}.relation`, i === 0 ? "disjoint" : "intersection_two");
    skip(C, [`${f}.circuit_sha256`], "hash of the Python encoding");
    skip(C, [`${f}.dummy_coordinate_unused`, `${f}.nested_role_incidences`], "label algebra and role compilation: circuit validity, not checked here");
  });
  // guard
  C.recomputed("guard.B", r.guard.B);
  C.recomputed("guard.C0", r.guard.C0);
  C.recomputed("guard.E", r.guard.E);
  C.recomputed("guard.scalar_depth_bound", nw.I * r.opsBound);
  C.recomputed("depth_hypothesis", nw.I * r.opsBound + 4n * nw.s + 4n * nw.W + 4n < r.guard.E && nw.s < nw.m ** 5n);
  // assembly
  const a = "assembly";
  for (const [cf, ts] of PARAM_FIELDS) C.input(`${a}.parameters.${cf}`, (p as unknown as Record<string, Q>)[ts]);
  for (const [k, gk] of Object.entries(r.margins)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`${a}.margins.${k}`, gk);
  C.recomputed(`${a}.minimum_margin`, r.G);
  C.recomputed(`${a}.recurrence.internal`, r.exponents.chi);
  C.recomputed(`${a}.recurrence.layer`, r.exponents.layer);
  C.recomputed(`${a}.recurrence.leaf`, r.exponents.leaf);
  C.input(`${a}.recurrence.preprocessing`, r.exponents.reserve);
  const byName = new Map(compactParameterChecks(p).map((k) => [k.name, slack(k)]));
  let allPos = true;
  for (const [cert, ts] of Object.entries(SLACKS_COMPACT)) {
    const s = byName.get(ts);
    if (!s) throw new Error(`no check named ${ts}`);
    if (s.num <= 0n) allPos = false;
    (PARAM_SLACKS.has(cert) ? C.input.bind(C) : C.recomputed.bind(C))(`${a}.slacks.${cert}`, s);
  }
  C.recomputed(`${a}.all_slacks_positive`, allPos);
  // the physical audit at n = 6, 7: rank sums from the note's per-stage formula with R rebuilt at that size
  const audit = C.get("physical_phase_audit.invocations") as Record<string, string>[];
  audit.forEach((row, i) => {
    const nn = Number(row.n);
    const v = binom(nn, 3);
    const triples = v;
    const D = dyadicCircuit(Number(triples), disjointRequests(nn));
    const E = dyadicCircuit(Number(triples), intersectionTwoRequests(nn).requests);
    const R = BigInt(D.additions + D.outputs + E.additions + E.outputs);
    const h = BigInt(nn + 1);
    const m = h ** 3n;
    const aa = h ** BigInt(Number(row.stage) - 1);
    const rank = (R + h) * m + 2n * v * aa * (h - 1n) + 2n * h * h;
    const f = `physical_phase_audit.invocations.${i}`;
    C.recomputed(`${f}.rank_sum`, rank);
    C.recomputed(`${f}.independently_derived_rank_sum`, rank);
    C.recomputed(`${f}.decreasing_dimension`, h * h);
    C.recomputed(`${f}.physical_roles`, R + h + 2n * v);
    C.input(`${f}.n`, nn);
    C.input(`${f}.stage`, Number(row.stage));
    C.input(`${f}.reverse`, row.reverse);
    C.skip(`${f}.checked_incidences`, "role incidences of the PR's simulation");
  });
  skip(C, ["physical_phase_audit.all_three_tensor_stages", "physical_phase_audit.complete_data_center_side_paths", "physical_phase_audit.exhaustive_phase_addresses", "physical_phase_audit.rank_sum_formula_verified", "physical_phase_audit.unique_binary_transitions"], "phase and path simulation at n = 6, 7: circuit validity, not checked here");
  (C.get("small_audits") as Record<string, string>[]).forEach((row, i) => {
    const nn = Number(row.n);
    const v = binom(nn, 3);
    const D = dyadicCircuit(Number(v), disjointRequests(nn));
    const E = dyadicCircuit(Number(v), intersectionTwoRequests(nn).requests);
    const R = BigInt(D.additions + D.outputs + E.additions + E.outputs);
    C.input(`small_audits.${i}.n`, nn);
    C.recomputed(`small_audits.${i}.scalar_basis_directions`, R + BigInt(nn + 1) + 2n * v);
    skip(C, ["arbitrary_scratch_basis_checked", "both_orientations", "direct_binary_residual_checks", "random_dyadic_cases", "three_shear_signed_exchange"].map((k) => `small_audits.${i}.${k}`), "scalar simulation: circuit validity, not checked here");
  });
  C.skip("missing_dummy_negative_control_rejected", "label algebra negative control, not checked here");
  C.input("repository_base", BASE);
  for (const f of Object.keys(C.get("retained_source_sha256") as object)) cloneHash(C, `retained_source_sha256.${f}`, BASE, f);
  for (const f of Object.keys(C.get("source_sha256") as object)) cloneHash(C, `source_sha256.${f}`, PR8_HEAD, `research/geometric-complex/${f}`);
  skip(C, ["scope", "status", "upstream_commit"]);
  return C.finish(print);
}

/** PR 8's bit screen (not part of its witness): circuits rebuilt at 30..70, cases and winner recomputed. */
export async function comparePR8Screen(print = true, cert?: unknown) {
  const C = new Comparator("PR8 bit-screen.json", cert ?? (await readCert("pr8-bit-screen.json")));
  const sc = bitScreen();
  for (const [x, ct] of sc.counts) {
    C.recomputed(`circuit_counts.${x}.additions`, ct.additions);
    C.recomputed(`circuit_counts.${x}.partial_outputs`, ct.outputs);
    C.recomputed(`circuit_counts.${x}.side_roles`, ct.R);
    C.recomputed(`circuit_counts.${x}.v`, binom(x, 3));
  }
  C.input("middle_sizes", [...sc.counts.keys()].join(","));
  C.input("outer_sizes", [...sc.counts.keys()].join(","));
  C.recomputed("pairs_examined", sc.pairs);
  C.recomputed("positive_deficit_cases", sc.cases);
  const w = sc.winner;
  for (const [f, val] of [["L", w.L], ["N", w.N], ["W", w.W], ["eta", w.eta], ["m", w.m], ["middle", w.y], ["outer", w.x]] as const) C.recomputed(`winner.${f}`, val);
  const lo = parseQ(String(C.get("winner.saving_lower")));
  const hi = parseQ(String(C.get("winner.saving_upper")));
  C.otherMethod("winner.saving_lower", le(lo, w.upper) && sc.unique, "a valid lower bound (below the TS upper enclosure); the TS enclosures also make the winner unique");
  C.otherMethod("winner.saving_upper", le(w.lower, hi), "a valid upper bound (above the TS lower enclosure)");
  skip(C, ["scope", "status"]);
  skip(C, ["winner_audits.frames.forward_frames_nested", "winner_audits.frames.reverse_complement_frames_nested", "winner_audits.frames.nondegeneracy", "winner_audits.global_circuit.circuit_sha256", "winner_audits.local.circuit_sha256"], "frame flags, descriptive strings and Python hashes");
  const r50 = sc.counts.get(50)!;
  C.recomputed("winner_audits.frames.roles", r50.R);
  C.recomputed("winner_audits.global_circuit.additions", r50.additions);
  C.recomputed("winner_audits.global_circuit.partial_outputs", r50.outputs);
  C.recomputed("winner_audits.global_circuit.roles", r50.R);
  C.input("winner_audits.global_circuit.h", 50);
  C.input("winner_audits.global_circuit.inputs", 19600);
  skip(C, ["winner_audits.global_circuit.all_additions_disjoint", "winner_audits.global_circuit.all_partial_outputs_exact", "winner_audits.global_circuit.every_node_has_common_point", "winner_audits.global_circuit.merged_additions", "winner_audits.local.additions", "winner_audits.local.all_additions_disjoint", "winner_audits.local.all_output_supports_exact", "winner_audits.local.inputs", "winner_audits.local.n", "winner_audits.local.nonzero_coefficients", "winner_audits.local.outputs", "winner_audits.local.scratch_roles"], "the published h = 50 circuit: recomputed by B1 of `bun run check` (and compared there with paired-network.json)");
  return C.finish(print);
}

// ------------------------------------------------------------------ PRs 9 to 13 (8 October, later)
// Certificates: pr9-prime-field-followup.json, pr10-batched-network.json,
// pr10-controlled-bit-rank-moment.json, pr11-geometric-dimensions-report.json,
// pr12-batched-followup.json, pr13-source-frame-network.json (SOURCES.txt).

/** Classify every leaf not yet listed, at the largest subtree with nothing listed, as "not compared". */
function skipRest(C: Comparator, why: string) {
  const listed = (p: string) => C.rows.some((r) => r.field === p || r.field.startsWith(p + ".") || p.startsWith(r.field + "."));
  const walk = (o: unknown, p: string) => {
    if (p && !listed(p)) return C.skip(p, why);
    if (p && C.rows.some((r) => r.field === p)) return;
    if (o !== null && typeof o === "object") {
      const entries = Array.isArray(o) ? o.map((v, i) => [String(i), v] as const) : Object.entries(o as Record<string, unknown>);
      for (const [k, v] of entries) walk(v, p ? `${p}.${k}` : k);
    }
  };
  walk(C.cert, "");
}

/** The batched assembly block shared by PRs 10, 12, 13. */
function batchedAssembly(C: Comparator, pre: string, p: CompactParams, mg: Record<string, Q>, G: Q, gk: { E: bigint; Cdep: bigint; C0: bigint; C1: Q }) {
  for (const [cf, ts] of PARAM_FIELDS) C.input(`${pre}.parameters.${cf}`, (p as unknown as Record<string, Q>)[ts]);
  for (const [k, g] of Object.entries(mg)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`${pre}.margins.${k}`, g);
  C.recomputed(`${pre}.minimum_margin`, G);
  C.recomputed(`${pre}.absorption_gap`, sub(G, p.kappa));
  C.recomputed(`${pre}.guard.E`, gk.E);
  C.recomputed(`${pre}.guard.dependency_constant`, gk.Cdep);
  C.recomputed(`${pre}.guard.C0`, gk.C0);
  C.recomputed(`${pre}.guard.C1`, gk.C1);
  const x = { tau: p.tau, chi: p.tau, leaf: add(p.sigma, mul(p.beta, sub(ONE, p.sigma))) };
  C.recomputed(`${pre}.recurrence.internal`, x.chi);
  C.recomputed(`${pre}.recurrence.layer`, x.chi);
  C.recomputed(`${pre}.recurrence.leaf`, x.leaf);
  // the named constraint slacks: each must equal one of the 29 recomputed slacks
  const table = slackTable(p as any, x.chi, x.leaf).map(([, v]) => v);
  const cons = C.get(`${pre}.constraints`) as Record<string, string>;
  for (const k of Object.keys(cons)) {
    const v = parseQ(String(cons[k]));
    C.otherMethod(`${pre}.constraints.${k}`, table.some((t) => eq(t, v)), "equals one of the 29 recomputed slacks (names matched by value)");
  }
}

const momentFields = (C: Comparator, pre: string, items: { r: Q; w: Q }[], keysR: string, keysW: string, ells?: Q[], keysL?: string) => {
  items.forEach((it, i) => {
    C.recomputed(`${pre}.${keysR}.${i}`, it.r);
    C.recomputed(`${pre}.${keysW}.${i}`, it.w);
    if (ells && keysL) C.input(`${pre}.${keysL}.${i}`, ells[i]!);
  });
};

export async function comparePR10(print = true) {
  const r = pr10().values;
  const C = new Comparator("PR10 certificates/batched-network.json", await readCert("pr10-batched-network.json"));
  const st = STATED_PR10;
  const ctrlLogs = [...st.midLogs, st.log28];
  for (const [pre, ctrl] of [["bit", r.ctrl], ["", r.ctrl]] as const) void pre, void ctrl;
  const bitBlock = (C: Comparator, pre: string) => {
    const P = pre ? `${pre}.` : "";
    C.recomputed(`${P}counts.N`, r.bit.N);
    C.recomputed(`${P}counts.W`, r.bit.W);
    C.recomputed(`${P}counts.deficit`, r.bit.D);
    C.recomputed(`${P}counts.decreasing_dimension`, r.bit.L);
    C.recomputed(`${P}counts.eta`, r.bit.eta);
    C.recomputed(`${P}counts.original_rank_sum`, r.bit.s);
    C.recomputed(`${P}counts.singleton_calls`, r.ctrl.S);
    C.input(`${P}counts.roles_per_invocation`, st.R);
    C.recomputed(`${P}counts.m`, r.bit.m);
    C.recomputed(`${P}counts.v`, r.bit.v);
    C.input(`${P}counts.h`, 28);
    C.input(`${P}bit_saving`, st.a);
    C.recomputed(`${P}tau`, sub(ONE, st.a));
    momentFields(C, P.slice(0, -1) || "", [], "", "");
    r.ctrl.items.forEach((it, i) => {
      C.recomputed(`${P}normalized_widths.${i}`, it.r);
      C.recomputed(`${P}rank_mass_weights.${i}`, it.w);
      C.input(`${P}logarithm_upper_bounds.${i}`, ctrlLogs[i]!);
    });
    C.recomputed(`${P}moment_upper`, r.ctrlB.bound);
    C.recomputed(`${P}strict_gap`, r.ctrlB.gap);
    const cls = (C.get(`${P}counts.bulk_classes`) as unknown[]).length;
    for (let i = 0; i < cls; i++) {
      C.recomputed(`${P}counts.bulk_classes.${i}.copies`, i === 2 ? 2n * r.bit.N : r.bit.v * r.bit.v * st.R);
      C.recomputed(`${P}counts.bulk_classes.${i}.original_rank`, st.ranks[i]!);
      C.recomputed(`${P}counts.bulk_classes.${i}.chunk_digits`, st.widths[i]!);
      C.recomputed(`${P}counts.bulk_classes.${i}.singleton_pivots`, i === 1 ? 0n : st.singles[i]!);
    }
    C.recomputed(`${P}counts.bulk_classes.1.additional_corner_chunk_digits`, 784n);
    [st.widths[0]!, st.widths[1]!, st.widths[2]!, 784n].forEach((w, i) => C.recomputed(`${P}counts.recursive_blocks.${i}.chunk_digits`, w));
  };
  bitBlock(C, "bit");
  C.input("complex.complex_saving", st.ac);
  C.recomputed("complex.sigma", sub(ONE, st.ac));
  for (const [k, v] of [["L", r.complex.L], ["N", r.complex.N], ["W", r.complex.W], ["s", r.complex.s], ["eta", r.complex.eta], ["m", r.complex.m], ["v", r.complex.v], ["deficit", r.complex.D], ["side_roles", r.Rc], ["auxiliary_roles", r.Rc + 29n], ["singleton_calls", r.cx.S]] as const) C.recomputed(`complex.counts.${k}`, v);
  C.input("complex.counts.h", 28);
  [0, 1].forEach((i) => {
    C.recomputed(`complex.counts.bulk_classes.${i}.copies`, r.Bc);
    C.recomputed(`complex.counts.bulk_classes.${i}.rank`, st.cRanks[i]!);
  });
  r.cx.items.forEach((it, i) => {
    C.recomputed(`complex.normalized_widths.${i}`, it.r);
    C.recomputed(`complex.rank_mass_weights.${i}`, it.w);
    C.input(`complex.logarithm_upper_bounds.${i}`, st.cLogs[i]!);
  });
  C.recomputed("complex.moment_upper", r.cxB.bound);
  C.recomputed("complex.strict_gap", r.cxB.gap);
  batchedAssembly(C, "assembly", r.params, r.margins, r.G, r.guard);
  const gb = bulkPathBounds(r.complex.m, 28n, st.cRanks);
  C.recomputed("assembly.guard.path_moment_upper.no_bulk", gb.first);
  C.recomputed("assembly.guard.path_moment_upper.rank_21896", gb.rows[0]!.bound);
  C.recomputed("assembly.guard.path_moment_upper.rank_21168", gb.rows[1]!.bound);
  C.recomputed("assembly.guard.q", gb.qq);
  C.recomputed("assembly.guard.at_most_one_selected_edge_per_path", gb.atMostOne);
  C.recomputed("assembly.guard.theta_slack", sub(q(999n, 1000n), gb.rows[0]!.bound));
  C.recomputed("assembly.dyadic_gap", sub(r.params.kappa, twoPow(-23)));
  skipRest(C, "label, input restated, log enclosure of another method, or source hash");
  const a = C.finish(print);
  const D = new Comparator("PR10 certificates/controlled-bit-rank-moment.json", await readCert("pr10-controlled-bit-rank-moment.json"));
  bitBlock(D, "");
  skipRest(D, "label, dependency text, or log enclosure of another method");
  const b = D.finish(print);
  return { DIFFER: a.DIFFER + b.DIFFER };
}

export async function comparePR13(print = true) {
  const r = pr13().values;
  const st = STATED_PR13;
  const C = new Comparator("PR13 certificates/source-frame-network.json", await readCert("pr13-source-frame-network.json"));
  for (const [k, v] of [["N", r.bit.N], ["W", r.bit.W], ["deficit", r.bit.D], ["eta", r.bit.eta], ["original_rank_sum", r.bit.s], ["singleton_calls", r.sf.S], ["previous_singleton_calls", STATED_PR10.S1], ["m", r.bit.m], ["v", r.bit.v], ["exit_rank", 21924n], ["exit_block", 21896n], ["exit_corner_pivots", 28n], ["removed_entrance_rank", 756n], ["stage_two_auxiliary_roles", st.B]] as const) C.recomputed(`bit.counts.${k}`, v);
  C.input("bit.counts.roles_per_invocation", st.R);
  C.input("bit.counts.h", 28);
  [st.widths[0]!, st.widths[1]!, st.widths[2]!].forEach((w, i) => C.recomputed(`bit.counts.recursive_blocks.${i}.chunk_digits`, w));
  r.sf.items.forEach((it, i) => {
    C.recomputed(`bit.normalized_widths.${i}`, it.r);
    C.recomputed(`bit.rank_mass_weights.${i}`, it.w);
    C.input(`bit.logarithm_upper_bounds.${i}`, st.logs[i]!);
  });
  C.recomputed("bit.moment_upper", r.b.bound);
  C.recomputed("bit.strict_gap", r.b.gap);
  C.input("bit.bit_saving", st.a);
  C.recomputed("bit.tau", sub(ONE, st.a));
  for (const [k, v] of [["L", r.complex.L], ["N", r.complex.N], ["W", r.complex.W], ["s", r.complex.s], ["eta", r.complex.eta], ["deficit", r.complex.D], ["singleton_calls", r.cw.S], ["previous_singleton_calls", STATED_PR10.Sc], ["m", r.complex.m], ["v", r.complex.v]] as const) C.recomputed(`complex.counts.${k}`, v);
  r.cw.items.forEach((it, i) => {
    C.recomputed(`complex.normalized_widths.${i}`, it.r);
    C.recomputed(`complex.rank_mass_weights.${i}`, it.w);
    C.input(`complex.logarithm_upper_bounds.${i}`, st.cLogs[i]!);
  });
  C.recomputed("complex.moment_upper", r.c.bound);
  C.recomputed("complex.strict_gap", r.c.gap);
  C.input("complex.complex_saving", st.ac);
  C.recomputed("complex.sigma", sub(ONE, st.ac));
  C.recomputed("complex.counts.bulk_classes.2.copies", 2n * r.complex.v ** 3n);
  const gk = bulkGuardConstants(r.complex.W, r.complex.m, r.params.beta, r.params.zeta);
  batchedAssembly(C, "assembly", r.params, r.margins, r.G, gk);
  const gb = bulkPathBounds(r.complex.m, 28n, [21896n, 21168n, 21141n]);
  C.recomputed("assembly.guard.path_moment_upper.rank_21141", gb.rows[2]!.bound);
  C.recomputed("assembly.dyadic_gap", sub(r.params.kappa, twoPow(-21)));
  C.recomputed("improvement_over_PR10", div(r.params.kappa, STATED_PR10.table[25]!));
  skipRest(C, "label, input restated, or source hash");
  return C.finish(print);
}

export async function comparePR12(print = true) {
  const r = pr12().values;
  const C = new Comparator("PR12 research/batched-followup/certificate.json", await readCert("pr12-batched-followup.json"));
  for (const [k, v] of [["N", r.bit.N], ["W", r.bit.W], ["deficit", r.bit.D], ["decreasing_dimension", r.bit.L], ["eta", r.bit.eta], ["original_rank_sum", r.bit.s], ["singleton_calls", r.w.S], ["m", r.bit.m], ["v", r.bit.v]] as const) C.recomputed(`bit.counts.${k}`, v);
  C.input("bit.counts.roles_per_invocation", STATED_PR12.R);
  r.w.items.forEach((it, i) => {
    C.recomputed(`bit.ratios.${i}`, it.r);
    C.recomputed(`bit.weights.${i}`, it.w);
    C.otherMethod(`bit.log_upper_bounds.${i}`, (() => {
      const L = parseQ(String(C.get(`bit.log_upper_bounds.${i}`)));
      return le(logInverseEnclosure(it.r).upper, L) && lt(L, add(logInverseEnclosure(it.r).upper, q(1n, 10n ** 9n)));
    })(), "a valid upper bound of log(1/r) within 10^-9 of the TS enclosure (the TS run rounds its own)");
  });
  C.otherMethod("bit.strict_gap", (() => {
    const g = parseQ(String(C.get("bit.strict_gap")));
    return lt(q(9n, 10n ** 12n), g) && lt(q(9n, 10n ** 12n), r.b.gap);
  })(), "both gaps exceed 9*10^-12 (log bounds rounded independently)");
  C.input("bit.bit_saving", STATED_PR12.a);
  C.recomputed("producer.checked.role_upper_bound", r.bit.v > 0n ? STATED_PR12.c + r.Q : 0n);
  batchedAssembly(C, "assembly", r.params, r.margins, r.G, bulkGuardConstants(STATED_PR10.Wc, 21952n, r.params.beta, r.params.zeta));
  C.recomputed("kappa_ratio_to_pr10", div(r.params.kappa, STATED_PR10.table[25]!));
  skipRest(C, "h = 30 producer data not rebuilt, PR 10's complex block (entry 10), label or hash");
  return C.finish(print);
}

export async function comparePR9(print = true) {
  const r = pr9().values;
  const C = new Comparator("PR9 research/prime-field-followup/certificate.json", await readCert("pr9-prime-field-followup.json"));
  C.recomputed("independent_cpp_check.new_star_additions", r.stars.newStar);
  C.recomputed("selected_templates.selected_star_additions", r.stars.newStar);
  C.recomputed("selected_templates.saved_additions", 2623060 - r.stars.newStar);
  C.recomputed("independent_cpp_check.optimized_additions", r.c);
  C.recomputed("independent_cpp_check.role_upper_bound", r.R);
  C.recomputed("selected_templates.winners.large_first", r.stars.winners.large);
  C.recomputed("selected_templates.winners.large_first_reverse", r.stars.winners.largeReverse);
  C.recomputed("selected_templates.winners.published_greedy", r.stars.winners.published);
  for (const [k, v] of [["D", r.bit.D], ["L", r.bit.L], ["N", r.bit.N], ["W", r.bit.W], ["eta", r.bit.eta], ["s", r.bit.s], ["roles", r.R], ["m", r.bit.m], ["v", r.bit.v]] as const) C.recomputed(`witness.bit.${k}`, v);
  for (const [cf, ts] of PARAM_FIELDS) C.input(`witness.parameters.${cf}`, (r.params as unknown as Record<string, Q>)[ts]);
  for (const [k, g] of Object.entries(r.margins)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`witness.margins.${k}`, g);
  C.recomputed("witness.minimum_margin", r.G);
  C.recomputed("witness.absorption_gap", sub(r.G, r.params.kappa));
  C.recomputed("witness.headline_ratio_to_pr7", div(r.params.kappa, q(373n, 10n ** 11n)));
  const gk = compactGuardConstantsFor(r.complex.W, r.complex.s, r.complex.m, r.params.zeta);
  C.recomputed("witness.guard.E", gk.E);
  C.recomputed("witness.guard.B", gk.B);
  C.recomputed("witness.guard.C0", gk.C0);
  for (const [k, v] of [["W", r.complex.W], ["s", r.complex.s], ["eta", r.complex.eta], ["L", r.complex.L], ["N", r.complex.N], ["D", r.complex.D]] as const) C.recomputed(`witness.retained_complex.${k}`, v);
  const cons = C.get("witness.constraints") as Record<string, string>;
  const all = fastParameterChecks(r.params).map((k) => slack(k));
  for (const k of Object.keys(cons)) C.otherMethod(`witness.constraints.${k}`, all.some((t) => eq(t, parseQ(String(cons[k])))) || lt(q(0n), parseQ(String(cons[k]))), "positive (matched by value where the PR 5 system has the same slack)");
  skipRest(C, "PR 7's inherited fields (entry 7), template records, label or hash");
  return C.finish(print);
}

export async function comparePR11(print = true) {
  const r = pr11().values as { rows: { h: number; R: bigint; lower: Q; upper: Q }[] };
  const C = new Comparator("PR11 research/geometric-dimensions/report.json", await readCert("pr11-geometric-dimensions-report.json"));
  const dims = C.get("dimensions") as unknown[];
  dims.forEach((_, i) => {
    const h = Number(C.get(`dimensions.${i}.h`));
    const row = r.rows.find((x) => x.h === h)!;
    C.input(`dimensions.${i}.roles`, row.R);
    C.recomputed(`dimensions.${i}.eta`, primeFieldBitNetwork(h, row.R).eta);
    C.otherMethod(`dimensions.${i}.exact_saving_upper`, le(row.lower, parseQ(String(C.get(`dimensions.${i}.exact_saving_upper`)))) && lt(parseQ(String(C.get(`dimensions.${i}.exact_saving_upper`))), q(761n, 10n ** 11n)), "at least the TS lower enclosure and below 761/10^11");
  });
  skipRest(C, "producer data not rebuilt at h != 28, labels, hashes, or checked separately in entry 11");
  return C.finish(print);
}


// ------------------------------------------------------------------ PRs 14 to 16 (8 October, later)
// Certificates: pr14-source-frame-corners.json, pr14-controlled-corners.json,
// pr15-source-frame-stream-witness.json, pr16-nested-source.json (SOURCES.txt).

/** Moment fields: ratios and weights recomputed; the certificate's log bounds checked as valid upper bounds; moment and gap recomputed* from those bounds. */
function momentBlock(C: Comparator, pre: string, items: { r: Q; w: Q }[], a: Q, keys: { r?: string; w: string; l: string; up: string; gap?: string }, near: Q) {
  const ells: Q[] = [];
  items.forEach((it, i) => {
    if (keys.r) C.recomputed(`${pre}.${keys.r}.${i}`, it.r);
    C.recomputed(`${pre}.${keys.w}.${i}`, it.w);
    const L = parseQ(String(C.get(`${pre}.${keys.l}.${i}`)));
    ells.push(L);
    const own = logInverseEnclosure(it.r).upper;
    C.otherMethod(`${pre}.${keys.l}.${i}`, le(logInverseEnclosure(it.r).lower, L) && lt(own, L) && lt(L, add(own, near)), `a valid upper bound of log(1/r) (above this checker's upper enclosure, within ${show(near)})`);
  });
  const b = momentUpperBound(items, a, ells);
  C.recomputed(`${pre}.${keys.up}`, b.bound, true);
  if (keys.gap) C.recomputed(`${pre}.${keys.gap}`, b.gap, true);
  return b;
}

export async function comparePR14(print = true) {
  const r = pr14().values;
  const st = STATED_PR14;
  const p12 = pr12().values;
  const bitCounts = (C: Comparator) => {
    for (const [k, v] of [["N", r.bit.N], ["W", r.bit.W], ["deficit", r.bit.D], ["decreasing_dimension", r.bit.L], ["eta", r.bit.eta], ["original_rank_sum", r.bit.s], ["singleton_calls", p12.w.S], ["m", r.bit.m], ["v", r.bit.v]] as const) C.recomputed(`bit.counts.${k}`, v);
    C.input("bit.counts.roles_per_invocation", st.R);
    C.input("bit.counts.h", 30);
    const B = r.bit.v * r.bit.v * st.R;
    [[B, 26940n, 26880n, 60n], [B, 26100n, 25200n, 0n], [2n * r.bit.N, 26071n, 25142n, 929n]].forEach(([cp, rk, w, sg], i) => {
      C.recomputed(`bit.counts.bulk_classes.${i}.copies`, cp);
      C.recomputed(`bit.counts.bulk_classes.${i}.original_rank`, rk);
      C.recomputed(`bit.counts.bulk_classes.${i}.chunk_digits`, w);
      C.recomputed(`bit.counts.bulk_classes.${i}.singleton_pivots`, sg);
    });
    C.recomputed("bit.counts.bulk_classes.1.additional_corner_chunk_digits", 900n);
    [[B, 26880n], [B, 25200n], [2n * r.bit.N, 25142n], [B, 900n]].forEach(([cp, w], i) => {
      if (C.get(`bit.counts.recursive_blocks.${i}.chunk_digits`) === undefined) return;
      C.recomputed(`bit.counts.recursive_blocks.${i}.copies`, cp);
      C.recomputed(`bit.counts.recursive_blocks.${i}.chunk_digits`, w);
    });
  };
  // headline certificate
  const C = new Comparator("PR14 research/source-frame-corners/certificate.json", await readCert("pr14-source-frame-corners.json"));
  bitCounts(C);
  C.recomputed("bit.singleton_calls", r.w.S);
  r.w.items.slice(1).forEach((it, i) => {
    C.recomputed(`bit.blocks.${i}.chunk_digits`, it.t);
    C.recomputed(`bit.blocks.${i}.copies`, it.copies);
  });
  momentBlock(C, "bit", r.w.items, st.a, { r: "ratios", w: "weights", l: "log_upper_bounds", up: "moment_upper", gap: "strict_gap" }, q(1n, 10n ** 10n));
  C.input("bit.bit_saving", st.a);
  for (const [k, v] of [["L", r.complex.L], ["N", r.complex.N], ["W", r.complex.W], ["s", r.complex.s], ["eta", r.complex.eta], ["deficit", r.complex.D], ["singleton_calls", r.cw.S], ["previous_singleton_calls", STATED_PR10.Sc], ["m", r.complex.m], ["v", r.complex.v], ["side_roles", 93838n], ["auxiliary_roles", 93867n]] as const) C.recomputed(`complex.counts.${k}`, v);
  C.input("complex.counts.h", 28);
  [[STATED_PR10.Bc, 21896n], [STATED_PR10.Bc, 21168n], [2n * r.complex.v ** 3n, 21141n]].forEach(([cp, rk], i) => {
    C.recomputed(`complex.counts.bulk_classes.${i}.copies`, cp);
    C.recomputed(`complex.counts.bulk_classes.${i}.rank`, rk);
  });
  r.cw.items.forEach((it, i) => {
    C.recomputed(`complex.normalized_widths.${i}`, it.r);
    C.recomputed(`complex.rank_mass_weights.${i}`, it.w);
    C.input(`complex.logarithm_upper_bounds.${i}`, STATED_PR13.cLogs[i]!);
  });
  C.recomputed("complex.moment_upper", r.c.bound);
  C.recomputed("complex.strict_gap", r.c.gap);
  C.input("complex.complex_saving", st.ac);
  C.recomputed("complex.sigma", sub(ONE, st.ac));
  const gk = bulkGuardConstants(r.complex.W, r.complex.m, r.params.beta, r.params.zeta);
  batchedAssembly(C, "assembly", r.params, r.margins, r.G, gk);
  const gb = bulkPathBounds(r.complex.m, 28n, [21896n, 21168n, 21141n]);
  C.recomputed("assembly.guard.path_moment_upper.no_bulk", gb.first);
  gb.rows.forEach((row) => C.recomputed(`assembly.guard.path_moment_upper.rank_${row.a}`, row.bound));
  C.recomputed("assembly.guard.q", gb.qq);
  C.recomputed("assembly.guard.at_most_one_selected_edge_per_path", gb.atMostOne);
  C.recomputed("assembly.guard.theta_slack", sub(q(999n, 1000n), gb.rows[0]!.bound));
  C.recomputed("ratio_to_pr13", div(r.params.kappa, q(7699n, 10n ** 10n)));
  skipRest(C, "label, input restated, h = 3/4 matrix controls (not rebuilt), commit or hash");
  const a = C.finish(print);
  // held-back controlled-corners certificate
  const D = new Comparator("PR14 research/controlled-corners/certificate.json", await readCert("pr14-controlled-corners.json"));
  bitCounts(D);
  D.recomputed("bit.singleton_calls", r.cc.w.S);
  r.cc.w.items.slice(1).forEach((it, i) => {
    D.recomputed(`bit.blocks.${i}.chunk_digits`, it.t);
    D.recomputed(`bit.blocks.${i}.copies`, it.copies);
  });
  momentBlock(D, "bit", r.cc.w.items, st.ccA, { r: "ratios", w: "weights", l: "log_upper_bounds", up: "moment_upper", gap: "strict_gap" }, q(1n, 10n ** 10n));
  D.input("bit.bit_saving", st.ccA);
  const p10 = pr10().values;
  for (const [k, v] of [["L", p10.complex.L], ["N", p10.complex.N], ["W", p10.complex.W], ["s", p10.complex.s], ["eta", p10.complex.eta], ["deficit", p10.complex.D], ["singleton_calls", p10.cx.S], ["m", p10.complex.m], ["v", p10.complex.v], ["side_roles", 93838n], ["auxiliary_roles", 93867n]] as const) D.recomputed(`complex.counts.${k}`, v);
  D.input("complex.counts.h", 28);
  [0, 1].forEach((i) => {
    D.recomputed(`complex.counts.bulk_classes.${i}.copies`, STATED_PR10.Bc);
    D.recomputed(`complex.counts.bulk_classes.${i}.rank`, STATED_PR10.cRanks[i]!);
  });
  p10.cx.items.forEach((it, i) => {
    D.recomputed(`complex.normalized_widths.${i}`, it.r);
    D.recomputed(`complex.rank_mass_weights.${i}`, it.w);
    D.input(`complex.logarithm_upper_bounds.${i}`, STATED_PR10.cLogs[i]!);
  });
  D.recomputed("complex.moment_upper", p10.cxB.bound);
  D.recomputed("complex.strict_gap", p10.cxB.gap);
  D.input("complex.complex_saving", STATED_PR10.ac);
  D.recomputed("complex.sigma", sub(ONE, STATED_PR10.ac));
  batchedAssembly(D, "assembly", r.pcc, r.cc.margins, r.cc.G, gk);
  const gb2 = bulkPathBounds(r.complex.m, 28n, [21896n, 21168n]);
  D.recomputed("assembly.guard.path_moment_upper.no_bulk", gb2.first);
  gb2.rows.forEach((row) => D.recomputed(`assembly.guard.path_moment_upper.rank_${row.a}`, row.bound));
  D.recomputed("assembly.guard.q", gb2.qq);
  D.recomputed("assembly.guard.at_most_one_selected_edge_per_path", gb2.atMostOne);
  D.recomputed("assembly.guard.theta_slack", sub(q(999n, 1000n), gb2.rows[0]!.bound));
  D.recomputed("ratio_to_pr12", div(r.pcc.kappa, q(12649n, 10n ** 11n)));
  skipRest(D, "label, input restated, matrix controls (not rebuilt), log enclosure intervals of another method, or hash");
  const b = D.finish(print);
  return { DIFFER: a.DIFFER + b.DIFFER };
}

/** The rho = 3/2 guard block shared by PRs 15 and 16 (field names differ). */
function rhoGuardBlock(C: Comparator, pre: string, g: { E: bigint; Cdep: bigint; C0: bigint; C1: Q; qq: bigint }, names: { dep: string }) {
  C.recomputed(`${pre}.E`, g.E);
  C.recomputed(`${pre}.${names.dep}`, g.Cdep);
  C.recomputed(`${pre}.C0`, g.C0);
  C.recomputed(`${pre}.C1`, g.C1);
  C.recomputed(`${pre}.q`, g.qq);
  C.input(`${pre}.rho`, q(3n, 2n));
}

export async function comparePR15(print = true) {
  const r = pr15().values;
  const st = STATED_PR15;
  const C = new Comparator("PR15 certificates/source-frame-stream-witness.json", await readCert("pr15-source-frame-stream-witness.json"));
  for (const [k, v] of [["W", r.bit.W], ["deficit", r.bit.D], ["eta", r.bit.eta], ["rank_sum", r.bit.s], ["singleton_calls", r.w.S], ["m", r.bit.m], ["v", r.bit.v], ["exit_corner_pivots", 30n], ["new_exit_rank", 26970n], ["removed_entrance_rank", 870n]] as const) C.recomputed(`bit.counts.${k}`, v);
  C.input("bit.counts.roles", st.R);
  C.input("bit.counts.h", 30);
  r.w.items.slice(1).forEach((it, i) => {
    C.recomputed(`bit.counts.recursive_blocks.${i}.width`, it.t);
    C.recomputed(`bit.counts.recursive_blocks.${i}.copies`, it.copies);
  });
  momentBlock(C, "bit", r.w.items, st.a, { r: "normalized_widths", w: "rank_mass_weights", l: "logarithm_upper_bounds", up: "moment_upper", gap: "strict_gap" }, q(1n, 10n ** 9n));
  C.input("bit.bit_saving", st.a);
  for (const [k, v] of [["W", r.complex.W], ["s", r.complex.s], ["eta", r.complex.eta], ["m", r.complex.m], ["v", r.complex.v], ["roles", 93838n]] as const) C.recomputed(`complex.counts.${k}`, v);
  C.input("complex.counts.h", 28);
  for (const [rk] of PR15_HISTOGRAM) C.input(`complex.counts.residual_histogram.${rk}`, r.hist.get(rk));
  const cb = momentBlock(C, "complex", r.cw.items, st.ac, { w: "rank_mass_weights", l: "logarithm_upper_bounds", up: "moment_upper" }, q(1n, 10n ** 9n));
  void cb;
  C.input("complex.complex_saving", st.ac);
  // next grid point: the conservative bound with the certificate's logs at a_c + 10^-12
  const cEll = r.cw.items.map((_, i) => parseQ(String(C.get(`complex.logarithm_upper_bounds.${i}`))));
  const next = momentUpperBound(r.cw.items, add(st.ac, q(1n, 10n ** 12n)), cEll);
  C.recomputed("complex.next_grid_moment", next.bound, true);
  const gk = { E: r.guard.E, Cdep: r.guard.Cdep, C0: r.guard.C0, C1: r.guard.C1, qq: r.guard.qq };
  for (const pre of ["complex.guard", "assembly.guard"]) {
    if (pre === "complex.guard") rhoGuardBlock(C, pre, gk, { dep: "dependency_constant" });
    else {
      C.recomputed(`${pre}.q`, gk.qq);
      C.input(`${pre}.rho`, q(3n, 2n));
    }
    C.recomputed(`${pre}.maximum_residual`, 21896n);
    C.input(`${pre}.path_moment_upper`, st.pathUpper);
    C.input(`${pre}.theta_upper`, q(999n, 1000n));
    C.recomputed(`${pre}.extremal_chunks.0`, r.guard.t.num === 1n ? sub(ONE, r.guard.t) : r.guard.t);
    C.recomputed(`${pre}.extremal_chunks.1`, r.guard.y);
  }
  batchedAssembly(C, "assembly", r.params, r.margins, r.G, gk);
  C.recomputed("assembly.dyadic_gap", sub(r.params.kappa, twoPow(-20)));
  C.recomputed("assembly.factor_over_PR13", div(r.params.kappa, q(7699n, 10n ** 10n)));
  C.recomputed("assembly.factor_over_aligned", div(r.params.kappa, q(1624n, 10n ** 12n)));
  skipRest(C, "h = 30 producer, frame and allocation audit (not rebuilt), small basis controls, references, label or hash");
  return C.finish(print);
}

export async function comparePR16(print = true) {
  const r = pr16().values;
  const st = STATED_PR16;
  const C = new Comparator("PR16 research/nested-source/certificate.json", await readCert("pr16-nested-source.json"));
  for (const [k, v] of [["N", r.bit.N], ["W", r.bit.W], ["deficit", r.bit.D], ["decreasing_dimension", r.bit.L], ["eta", r.bit.eta], ["original_rank_sum", r.bit.s], ["singleton_calls", r.w.S], ["m", r.bit.m], ["v", r.bit.v]] as const) C.recomputed(`bit.counts.${k}`, v);
  C.input("bit.counts.roles_per_invocation", st.R);
  C.input("bit.counts.h", 32);
  C.input("bit.a_b", st.a);
  C.recomputed("bit.tau", sub(ONE, st.a));
  C.recomputed("bit.above_two_to_minus_19", lt(twoPow(-19), st.a));
  // log enclosures are intervals: compare by overlap; the moment with their upper endpoints is recomputed*
  const ells: Q[] = [];
  r.w.items.forEach((it, i) => {
    C.recomputed(`bit.ratios.${i}`, it.r);
    C.recomputed(`bit.weights.${i}`, it.w);
    const lo = parseQ(String(C.get(`bit.log_enclosures.${i}.0`)));
    const hi = parseQ(String(C.get(`bit.log_enclosures.${i}.1`)));
    ells.push(hi);
    const e = logInverseEnclosure(it.r);
    C.otherMethod(`bit.log_enclosures.${i}`, le(lo, e.upper) && le(e.lower, hi) && lt(lo, hi), "the enclosure overlaps this checker's enclosure of log(1/r)");
  });
  const b = momentUpperBound(r.w.items, st.a, ells);
  C.recomputed("bit.moment_upper", b.bound, true);
  C.recomputed("bit.strict_gap", b.gap, true);
  for (const [k, v] of [["D", 18030055680n], ["L", r.complex.L], ["N", r.complex.N], ["W", r.complex.W], ["s", r.complex.s], ["eta", r.complex.eta], ["m", r.complex.m], ["v", r.complex.v], ["side_roles", 93838n], ["auxiliary_roles", 93867n], ["zero_rank_edges", 3n * r.complex.v * r.complex.v * st.zeroEdges]] as const) C.recomputed(`complex.global_counts.${k}`, v);
  C.input("complex.global_counts.h", 28);
  for (const [rk, cp] of r.hist) C.recomputed(`complex.global_histogram.${rk}`, cp);
  C.recomputed("complex.all_residuals_proper", [...r.hist.keys()].every((x) => x < r.complex.m));
  C.recomputed("complex.full_rank_residuals", [...r.hist.keys()].filter((x) => x === r.complex.m).length);
  C.recomputed("complex.rank_sum_matches", [...r.hist.entries()].reduce((acc, [x, c]) => acc + x * c, 0n) === r.complex.s);
  (C.get("complex.external_classes") as unknown[]).forEach((_, i) => {
    const rk = BigInt(String(C.get(`complex.external_classes.${i}.rank`)));
    const expect = new Map([[21896n, st.Bc], [21168n, st.Bc], [756n, st.Bc], [729n, 2n * r.complex.N], [21141n, 2n * r.complex.N]]);
    C.recomputed(`complex.external_classes.${i}.copies`, expect.get(rk));
  });
  for (const k of Object.keys(C.get("complex.complex_saving_moments") as Record<string, unknown>)) {
    const a = parseQ(k);
    const mine = momentUpperBound(r.cw.items, a, r.cOwn);
    const theirs = parseQ(String(C.get(`complex.complex_saving_moments.${k}.upper`)));
    C.otherMethod(`complex.complex_saving_moments.${k}`, lt(mine.bound, ONE) && lt(theirs, ONE) && String(C.get(`complex.complex_saving_moments.${k}.passed`)) === "true", `both bounds below 1 (TS gap ${toDecimal(mine.gap, 12)})`);
  }
  const g = r.guard;
  C.recomputed("complex.guard.E", g.E);
  C.recomputed("complex.guard.Cdep", g.Cdep);
  C.recomputed("complex.guard.C0", g.C0);
  C.recomputed("complex.guard.C1", g.C1);
  C.recomputed("complex.guard.q", g.qq);
  C.recomputed("complex.guard.M", 21896n);
  C.recomputed("complex.guard.remaining_rank", g.qq - 21896n);
  C.recomputed("complex.guard.path_moment_upper", g.pr16Bound);
  C.recomputed("complex.guard.largest_edge_power_upper", g.T);
  C.recomputed("complex.guard.remainder_power_upper", div(g.y, q(9n)));
  C.input("complex.guard.sqrt_remainder_reciprocal", 9);
  C.input("complex.guard.rho", q(3n, 2n));
  C.input("complex.guard.theta", q(999n, 1000n));
  C.input("complex.guard.beta", r.params.beta);
  C.input("complex.guard.zeta", r.params.zeta);
  for (const [cf, ts] of PARAM_FIELDS) C.input(`assembly.parameters.${cf}`, (r.params as unknown as Record<string, Q>)[ts]);
  for (const [k, gk] of Object.entries(r.margins)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`assembly.margins.${k}`, gk);
  C.recomputed("assembly.minimum_margin", r.G);
  C.recomputed("assembly.absorption_gap", sub(r.G, r.params.kappa));
  const x = { chi: r.params.tau, leaf: add(r.params.sigma, mul(r.params.beta, sub(ONE, r.params.sigma))) };
  C.recomputed("assembly.recurrence.internal", x.chi);
  C.recomputed("assembly.recurrence.layer", x.chi);
  C.recomputed("assembly.recurrence.leaf", x.leaf);
  const table = slackTable(r.params as any, x.chi, x.leaf).map(([, v]) => v);
  const cons = C.get("assembly.constraints") as Record<string, string>;
  for (const k of Object.keys(cons)) C.otherMethod(`assembly.constraints.${k}`, table.some((t) => eq(t, parseQ(String(cons[k])))), "equals one of the 29 recomputed slacks (names matched by value)");
  C.recomputed("assembly.dyadic_gap", sub(r.params.kappa, twoPow(-20)));
  C.recomputed("assembly.ratio_to_pr10", div(r.params.kappa, STATED_PR10.table[25]!));
  C.recomputed("assembly.ratio_to_pr12", div(r.params.kappa, q(12649n, 10n ** 11n)));
  C.recomputed("assembly.ratio_to_pr13", div(r.params.kappa, q(7699n, 10n ** 10n)));
  skipRest(C, "local schedule classes, complex log bound intervals and derivative bounds of another method, finite controls (not rebuilt), label, commit or hash");
  return C.finish(print);
}

if (import.meta.main) {
  const only = (process.argv.find((x) => x.startsWith("--only="))?.slice(7) ?? "1,2,3,4,4b,5,6,7,8,9,10,11,12,13,14,15,16").split(",");
  let differ = 0;
  if (only.includes("1")) differ += (await comparePR1()).DIFFER;
  if (only.includes("2")) differ += (await comparePR2()).DIFFER;
  if (only.includes("3")) differ += (await comparePR3()).DIFFER;
  if (only.includes("4")) differ += (await comparePR4()).DIFFER;
  if (only.includes("4b")) differ += (await comparePR4b()).DIFFER;
  if (only.includes("5")) differ += (await comparePR5()).DIFFER;
  if (only.includes("6")) differ += (await comparePR6()).DIFFER;
  if (only.includes("7")) differ += (await comparePR7()).DIFFER;
  if (only.includes("8")) {
    differ += (await comparePR8()).DIFFER;
    differ += (await comparePR8Screen()).DIFFER;
  }
  if (only.includes("9")) differ += (await comparePR9()).DIFFER;
  if (only.includes("10")) differ += (await comparePR10()).DIFFER;
  if (only.includes("11")) differ += (await comparePR11()).DIFFER;
  if (only.includes("12")) differ += (await comparePR12()).DIFFER;
  if (only.includes("13")) differ += (await comparePR13()).DIFFER;
  if (only.includes("14")) differ += (await comparePR14()).DIFFER;
  if (only.includes("15")) differ += (await comparePR15()).DIFFER;
  if (only.includes("16")) differ += (await comparePR16()).DIFFER;
  console.log(`\nCOMPARE PRs: ${differ === 0 ? "no disagreement" : `${differ} disagreement(s)`}`);
  if (differ > 0) process.exit(1);
}

