// Field-by-field comparison of the recomputed values with the repository's
// certificates (the Python output):
//   certificates/paired-network.json         preserved 2^-59 witness and the bit network
//   certificates/compact-control-layer.json  current compact-control witness
// Usage: `bun run compare` from independent/ts (add --only=59 or --only=compact).
// Exit code 1 on any disagreement. Statuses are explained in comparator.ts.

import { createHash } from "node:crypto";
import { bitNetwork, paired59, compactWitnessChecks, COMPLEX_H, type BitValues } from "./checks";
import { type Q, q, show, parseQ, eq, sub, twoPow, add, mul, le, lt, div, ONE } from "./rational";
import { slack, holds } from "./parameters";
import { Comparator, parseLossless } from "./comparator";
import { compactParams, type CompactParams } from "./compact/witness";
import { allocation, repairBound } from "./compact/layout";
import { ground } from "./networks";

const root = `${import.meta.dir}/../../..`;
export const readCert = async (name: string) => parseLossless(await Bun.file(`${root}/certificates/${name}`).text());

/** `cert` replaces the certificate read from disk (tests feed corrupted copies); `print` = false suppresses the table. */
export type CompareOptions = { cert?: unknown; print?: boolean };

// ---------------------------------------------------------------------------------------------------- 2^-59

export async function compare59(bitV: BitValues, opts: CompareOptions = {}) {
  const C = new Comparator("paired-network.json (2^-59 witness and bit network)", opts.cert ?? (await readCert("paired-network.json")));
  const v = { ...bitV, ...paired59(bitV).values };
  const g = v.ground;
  const bp = v.pairedBit;
  const cx = v.complex;
  const p = v.params;
  const L = v.localReport;
  const Gr = v.globalReport;

  // bit network
  C.input("bit_counts.h", 50);
  C.recomputed("bit_counts.v", g.v);
  C.recomputed("bit_counts.m", g.m);
  C.recomputed("bit_counts.N", g.N);
  C.recomputed("bit_counts.L", bp.L);
  C.recomputed("bit_counts.W", bp.W);
  C.recomputed("bit_counts.s", bp.s);
  C.recomputed("bit_counts.D", bp.deficit);
  C.recomputed("bit_counts.eta", bp.eta);
  C.recomputed("bit_counts.side_roles_per_invocation", v.R);
  C.input("bit_saving", p.a);
  C.recomputed("bit_deficit_slack", v.bitDeficitSlack);
  // complex network (h = 50)
  C.input("complex_counts.h", 50);
  C.recomputed("complex_counts.v", g.v);
  C.recomputed("complex_counts.m", g.m);
  C.recomputed("complex_counts.N", g.N);
  C.recomputed("complex_counts.Lc", cx.L);
  C.recomputed("complex_counts.Wc", cx.W);
  C.recomputed("complex_counts.sc", cx.s);
  C.recomputed("complex_counts.eta_c", cx.eta);
  C.input("complex_saving", p.ac);
  C.recomputed("complex_deficit_slack", v.complexDeficitSlack);
  // logarithm (same atanh method as the Python, because the note prescribes it)
  C.input("log_m_upper", v.L0);
  C.recomputed("log_enclosure.0", v.logm.lower);
  C.recomputed("log_enclosure.1", v.logm.upper);
  // local circuit
  C.input("local_circuit.n", L.n);
  C.input("local_circuit.inputs", L.outputs); // C(49,2) input nodes, allocated from n
  C.recomputed("local_circuit.additions", L.additions);
  C.input("local_circuit.outputs", L.outputs); // allocated as C(n,2)
  C.recomputed("local_circuit.nonzero_coefficients", L.nonzeroCoefficients);
  C.recomputed("local_circuit.scratch_roles", L.additions + L.outputs);
  C.recomputed("local_circuit.all_additions_disjoint", L.allAdditionsDisjoint);
  C.recomputed("local_circuit.all_output_supports_exact", L.allOutputSupportsExact);
  C.skip("local_circuit.circuit_sha256", "hash of the Python JSON encoding of node ids; not reproduced");
  // global circuit
  C.input("global_circuit.h", Gr.h);
  C.input("global_circuit.inputs", Number(g.v)); // one input node per triple, allocated as C(h,3)
  C.recomputed("global_circuit.additions", Gr.additions);
  C.recomputed("global_circuit.merged_additions", Gr.mergedAdditions);
  C.input("global_circuit.partial_outputs", Gr.partialOutputs); // allocated as h C(h-1,2)
  C.recomputed("global_circuit.roles", Gr.roles); // c + q with the recomputed c
  C.recomputed("global_circuit.all_additions_disjoint", Gr.allAdditionsDisjoint);
  C.recomputed("global_circuit.all_partial_outputs_exact", Gr.allPartialOutputsExact);
  C.recomputed("global_circuit.every_node_has_common_point", Gr.everyNodeHasCommonPoint);
  C.skip("global_circuit.circuit_sha256", "hash of the Python JSON encoding of node ids; not reproduced");
  // frames
  C.recomputed("frames.roles", Gr.roles);
  // The Python compiles every role and checks both frame directions per role. The TypeScript
  // argues from supports instead (global.ts header): disjoint additions plus a common point
  // in every node's support give both nestings. Its conclusion is the conjunction below.
  const supportArgument = Gr.allAdditionsDisjoint && Gr.everyNodeHasCommonPoint && Gr.allPartialOutputsExact && Gr.everyNodeUsed;
  const certTrue = (f: string) => String(C.get(f)) === "true";
  C.otherMethod("frames.forward_frames_nested", supportArgument && certTrue("frames.forward_frames_nested"), "support-level argument (Python: per compiled role)");
  C.otherMethod("frames.reverse_complement_frames_nested", supportArgument && certTrue("frames.reverse_complement_frames_nested"), "support-level argument (Python: per compiled role)");
  C.skip("frames.nondegeneracy", "descriptive string");
  // Gaussian
  C.recomputed("gaussian.alpha_exponent", add(q(1n, 4n), mul(q(1n, 4n), p.epsilon)));
  C.recomputed("gaussian.gamma_exponent", add(q(1n, 2n), mul(q(3n, 2n), p.epsilon)));
  C.recomputed("gaussian.gaussian_cost_exponent", add(add(q(3n, 4n), p.delta), mul(q(5n, 4n), p.epsilon)));
  for (const f of ["alpha_definition", "gamma_cutoff", "resampling_margin"]) C.skip(`gaussian.${f}`, "descriptive string");
  // stopped guard
  C.input("stopped_guard.h", 50);
  C.recomputed("stopped_guard.m", g.m);
  C.recomputed("stopped_guard.complex_s", cx.s);
  C.recomputed("stopped_guard.E", v.guard.E);
  C.recomputed("stopped_guard.B", v.guard.B);
  C.recomputed("stopped_guard.C0", v.guard.C0);
  C.input("stopped_guard.C1", p.C1);
  C.input("stopped_guard.beta", p.beta);
  C.recomputed("stopped_guard.one_piece_depth_exponent", sub(q(5n), mul(q(4n), p.beta)));
  C.recomputed("stopped_guard.depth_with_piece_count_exponent", add(sub(q(5n), mul(q(4n), p.beta)), q(1n, 2n)));
  C.recomputed("stopped_guard.s_below_m_fifth", cx.s < g.m ** 5n);
  C.skip("stopped_guard.scope", "descriptive string");
  // parameters (inputs) and margins
  const P = p as unknown as Record<string, Q>;
  for (const [cert, ts] of [["tau", "tau"], ["sigma", "sigma"], ["beta", "beta"], ["epsilon", "epsilon"], ["delta", "delta"], ["C1", "C1"], ["c", "c"], ["lam", "lambda"], ["lamp", "lambdaPrime"], ["kappa", "kappa"]] as const)
    C.input(`witness.parameters.${cert}`, P[ts]);
  for (const [k, gk] of Object.entries(v.margins)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`witness.margins.${k}`, gk); // g7 = epsilon
  C.recomputed("witness.minimum_margin", v.G);
  C.recomputed("witness.absorption_gap", sub(v.G, p.kappa));
  C.recomputed("witness.all_margins_at_least_twice_kappa", le(mul(q(2n), p.kappa), v.G));
  C.recomputed("witness.limiting_margins", Object.entries(v.margins).filter(([, gk]) => eq(gk, v.G)).map(([k]) => k).join(","));
  const byName = new Map(v.parameterChecks.map((k) => [k.name, slack(k)]));
  const inputSlacks = new Set(["tau_positive", "tau_below_one", "sigma_positive", "sigma_below_one", "beta_below_one", "c_positive", "epsilon_positive", "delta_positive", "kappa_positive", "lambda_below_one", "lambda_prime_below_one"]);
  const slackMap: Record<string, string> = {
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
  for (const [certName, tsName] of Object.entries(slackMap)) {
    const s = byName.get(tsName);
    if (!s) throw new Error(`no TypeScript check named ${tsName}`);
    (inputSlacks.has(certName) ? C.input.bind(C) : C.recomputed.bind(C))(`witness.constraint_slacks.${certName}`, s);
  }
  // The certificate records beta > 0 (slack beta, an input); the note's guard needs beta >= 9/10, checked separately.
  C.input("witness.constraint_slacks.beta_positive", p.beta);
  for (const f of ["slack_rule", "guard_model", "assembly_model", "generalized_beta"]) C.skip(`witness.${f}`, "descriptive label");
  // room left
  C.recomputed("fixed_network_ceiling.value", v.ceiling.value);
  C.recomputed("fixed_network_ceiling.strictly_below_2_to_minus_58", lt(v.ceiling.value, twoPow(-58)));
  C.skip("fixed_network_ceiling.formula", "descriptive string");
  C.skip("fixed_network_ceiling.scope", "descriptive string");
  for (const f of ["status", "scope", "upstream_commit"]) C.skip(f, "descriptive label");
  return C.finish(opts.print ?? true);
}

// ---------------------------------------------------------------------------------------------------- compact-control

/** Constraint-slack names of the certificate -> TypeScript check names (mapped after the list was written). */
const COMPACT_SLACKS: Record<string, string> = {
  tau_positive: "tau > 0",
  tau_below_one: "tau < 1",
  sigma_positive: "sigma > 0",
  sigma_below_one: "sigma < 1",
  beta_positive: "beta > 0",
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
  packed_overhead: "chi < lambda",
  leaf_cost: "sigma + beta(1-sigma) < lambda'",
  reserved_axes: "max{1-c,0} < lambda'",
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
/** Slacks that are a parameter itself or 1 minus a parameter. */
const PARAM_SLACKS = new Set(["tau_positive", "tau_below_one", "sigma_positive", "sigma_below_one", "beta_positive", "beta_below_one", "c_positive", "epsilon_positive", "delta_positive", "kappa_positive", "lambda_below_one", "lambda_prime_below_one"]);
const PARAM_FIELDS = [["tau", "tau"], ["sigma", "sigma"], ["beta", "beta"], ["epsilon", "epsilon"], ["delta", "delta"], ["C1", "C1"], ["c", "c"], ["lam", "lambda"], ["lamp", "lambdaPrime"], ["kappa", "kappa"]] as const;

/** One parameter set (main witness or a milestone) and its guard, recurrence, slacks and margins. */
function compareParameterSet(C: Comparator, prefix: string, p: CompactParams, h: number, fromCert: boolean) {
  const w = compactWitnessChecks(p, h);
  const P = p as unknown as Record<string, Q>;
  const inputRow = (path: string, x: unknown) => (fromCert ? C.skip(path, "input read from the certificate (not stated in the note)") : C.input(path, x));
  for (const [cert, ts] of PARAM_FIELDS) inputRow(`${prefix}.parameters.${cert}`, P[ts]);
  // guard
  inputRow(`${prefix}.guard.h`, h);
  inputRow(`${prefix}.guard.beta`, p.beta);
  inputRow(`${prefix}.guard.zeta`, p.zeta);
  inputRow(`${prefix}.guard.C1`, p.C1);
  C.recomputed(`${prefix}.guard.m`, w.m, fromCert);
  C.recomputed(`${prefix}.guard.s`, w.cx.s, fromCert);
  C.recomputed(`${prefix}.guard.E`, w.guard.E, fromCert);
  C.recomputed(`${prefix}.guard.B`, w.guard.B, fromCert);
  C.recomputed(`${prefix}.guard.C0`, w.guard.C0, fromCert);
  C.recomputed(`${prefix}.guard.one_piece_exponent`, sub(q(5n), mul(q(4n), p.beta)), fromCert);
  // recurrence exponents
  C.recomputed(`${prefix}.recurrence.internal`, w.exponents.chi, fromCert);
  C.recomputed(`${prefix}.recurrence.leaf`, w.exponents.leaf, fromCert);
  C.recomputed(`${prefix}.recurrence.layer`, w.exponents.layer, fromCert);
  if (fromCert) C.skip(`${prefix}.recurrence.preprocessing`, "max{1-c,0} with c read from the certificate");
  else C.input(`${prefix}.recurrence.preprocessing`, w.exponents.reserve); // 1 - c
  // slacks
  const byName = new Map(w.parameterChecks.map((k) => [k.name, slack(k)]));
  for (const [certName, tsName] of Object.entries(COMPACT_SLACKS)) {
    const s = byName.get(tsName);
    if (!s) throw new Error(`no TypeScript check named ${tsName}`);
    const path = `${prefix}.constraint_slacks.${certName}`;
    if (PARAM_SLACKS.has(certName)) fromCert ? C.skip(path, "a parameter, or 1 minus one, read from the certificate") : C.input(path, s);
    else C.recomputed(path, s, fromCert);
  }
  C.recomputed(`${prefix}.minimum_margin`, w.G, fromCert);
  C.recomputed(`${prefix}.absorption_gap`, sub(w.G, p.kappa), fromCert);
  // the TypeScript conditions on this parameter set (not certificate fields)
  const failing = [...w.parameterChecks, ...w.guardChecks].filter((k) => !holds(k)).map((k) => k.name);
  if (!lt(p.kappa, w.G)) failing.push("kappa < G");
  if (!w.complexSupported) failing.push("a_c below the actual complex saving");
  return { w, failing };
}

function paramsFromCert(o: any, zeta: Q): CompactParams {
  const r = (k: string) => parseQ(String(o[k]));
  const tau = r("tau");
  const sigma = r("sigma");
  return { a: sub(ONE, tau), ac: sub(ONE, sigma), tau, sigma, beta: r("beta"), epsilon: r("epsilon"), delta: r("delta"), C1: r("C1"), c: r("c"), lambda: r("lam"), lambdaPrime: r("lamp"), kappa: r("kappa"), zeta };
}

export async function compareCompact(opts: CompareOptions = {}) {
  const C = new Comparator("compact-control-layer.json (current witness)", opts.cert ?? (await readCert("compact-control-layer.json")));
  const p = compactParams();
  const main = compareParameterSet(C, "main", p, COMPLEX_H, false);
  const w = main.w;
  const g25 = ground(COMPLEX_H);
  // main-only fields
  C.input("main.complex_h", COMPLEX_H);
  for (const [k, gk] of Object.entries(w.margins)) (k === "g7" ? C.input.bind(C) : C.recomputed.bind(C))(`main.margins.${k}`, gk);
  const certEnc = (C.get("main.complex_saving_enclosure") as string[]).map(parseQ);
  C.otherMethod("main.complex_saving_enclosure.0", le(certEnc[0]!, w.enclosure.upper), "cert lower <= TS upper (TS: Mercator series; certificate: atanh series)");
  C.otherMethod("main.complex_saving_enclosure.1", le(w.enclosure.lower, certEnc[1]!), "TS lower <= cert upper (the two enclosures overlap)");
  // complex network h = 25
  C.input("complex_counts.h", COMPLEX_H);
  C.recomputed("complex_counts.m", w.m);
  C.recomputed("complex_counts.v", g25.v);
  C.recomputed("complex_counts.N", g25.N);
  C.recomputed("complex_counts.Wc", w.cx.W);
  C.recomputed("complex_counts.Lc", w.cx.L);
  C.recomputed("complex_counts.sc", w.cx.s);
  C.recomputed("complex_counts.eta_c", w.cx.eta);
  C.recomputed("complex_log_upper", w.logm.upper); // 24-term atanh enclosure (the paired note's method; the new note does not state one)
  C.recomputed("complex_deficit_slack", sub(w.cx.eta, mul(p.ac, w.logm.upper)));
  C.recomputed("bit_arity", ground(50).m);
  C.recomputed("complex_arity", w.m);
  C.recomputed("improvement_over_published_59", mul(p.kappa, twoPow(59)));
  // scoped ceiling: a different enclosure of the same real number a*/5
  const certUpper = parseQ(C.get("scoped_ceiling.upper") as string);
  const tsLower5 = div(w.enclosure.lower, q(5n));
  const tsUpper5 = div(w.enclosure.upper, q(5n));
  C.otherMethod("scoped_ceiling.upper", le(tsLower5, certUpper) && lt(certUpper, twoPow(-33)), "TS lower/5 <= cert upper < 2^-33");
  const certFrac = parseQ(C.get("scoped_ceiling.witness_fraction_of_upper") as string);
  C.otherMethod("scoped_ceiling.witness_fraction_of_upper", lt(q(99n, 100n), certFrac) && le(div(p.kappa, tsUpper5), certFrac) && le(certFrac, div(p.kappa, tsLower5)), "kappa/(TS upper/5) <= cert <= kappa/(TS lower/5), cert > 99/100");
  C.recomputed("scoped_ceiling.below_next_dyadic", lt(tsUpper5, twoPow(-33)));
  C.skip("scoped_ceiling.scope", "descriptive string");
  // proof hashes: integrity of the four notes in this checkout, not mathematics
  for (const f of ["notes/compact-control-guard.tex", "notes/compact-control-layout.tex", "notes/compact-control-movement.tex", "notes/independent-complex.tex"]) {
    const hash = createHash("sha256").update(new Uint8Array(await Bun.file(`${root}/${f}`).arrayBuffer())).digest("hex");
    C.recomputed(`proof_sha256.${f}`, hash);
  }
  // milestones: parameter sets read from the certificate, everything else recomputed
  const extra: string[] = [];
  for (const [key, h] of [["target_34", 25], ["target_39", 50]] as const) {
    const o = C.get(`milestones.${key}`) as any;
    const mp = paramsFromCert(o.parameters, parseQ(String(o.guard.zeta)));
    if (Number(o.guard.h) !== h) throw new Error(`unexpected h for ${key}`);
    const r = compareParameterSet(C, `milestones.${key}`, mp, h, true);
    extra.push(`${key}: TypeScript constraints, guard, kappa < G and complex support ${r.failing.length ? "FAIL " + r.failing.join("; ") : "all hold"}`);
  }
  // layout instances: (d, D, K, G) read from the certificate, field sizes recomputed from compact-control-layout.tex
  const allocs = C.get("allocation_controls") as any[];
  allocs.forEach((a, i) => {
    const pre = `allocation_controls.${i}`;
    const al = allocation(BigInt(a.d), BigInt(a.D), BigInt(a.K), BigInt(a.G), w.m, w.cx.W);
    for (const f of ["d", "D", "K", "G"]) C.skip(`${pre}.${f}`, "instance input read from the certificate");
    for (const f of ["compact_capacity", "row_chunks", "front_chunks", "back_chunks", "reserved_chunks", "recursion_depth_cap", "row_bits", "mode", "active_chunks", "preprocessed_chunks", "front_slack_bits", "back_slack_bits"] as const)
      C.recomputed(`${pre}.${f}`, al[f], true);
    const ok = al.rowRangeCoversWk0 && al.frontFieldsFit && al.backFieldFits && al.reservedCountBound;
    extra.push(`allocation ${i}: 2^(q0 K) >= W^k0, q_F K >= 2H, q_B K >= H, q_F + q_B <= 3dG/K + 2: ${ok ? "hold" : "FAIL"}`);
  });
  // repair instances: (p, n, K) read from the certificate
  const reps = C.get("repair_controls") as any[];
  reps.forEach((r, i) => {
    const pre = `repair_controls.${i}`;
    const rb = repairBound(BigInt(r.p), BigInt(r.n), BigInt(r.K));
    for (const f of ["p", "n", "K"]) C.skip(`${pre}.${f}`, "instance input read from the certificate");
    C.recomputed(`${pre}.G`, rb.G, true);
    C.recomputed(`${pre}.late_bad_fraction_upper`, rb.delta, true);
    C.recomputed(`${pre}.uniform_upper`, rb.uniform, true);
    extra.push(`repair ${i}: K at or above the cutoff and delta <= 5/(128 p^3): ${rb.cutoff && rb.ok ? "hold" : "FAIL"}`);
  });
  for (const f of ["status", "scope", "upstream_commit"]) C.skip(f, "descriptive label");
  if (main.failing.length) extra.push(`main: FAIL ${main.failing.join("; ")}`);
  const counts = C.finish(opts.print ?? true);
  if (opts.print ?? true) for (const e of extra) console.log(`  ${e}`);
  const extraFail = extra.some((e) => e.includes("FAIL"));
  return { ...counts, DIFFER: counts.DIFFER + (extraFail ? 1 : 0), extra };
}

// ---------------------------------------------------------------------------------------------------- run

if (import.meta.main) {
  const only = process.argv.find((x) => x.startsWith("--only="))?.slice("--only=".length) ?? "all";
  let differ = 0;
  if (only === "all" || only === "59") differ += (await compare59(bitNetwork({ alternative: false }).values)).DIFFER;
  if (only === "all" || only === "compact") differ += (await compareCompact()).DIFFER;
  console.log(`\nCOMPARE: ${differ === 0 ? "no disagreement" : `${differ} disagreement(s)`}`);
  if (differ > 0) process.exit(1);
}
