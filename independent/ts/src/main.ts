// Entry point.
//   bun run check            both witnesses (bit network, preserved 2^-59, current compact-control)
//   bun run check:59         bit network + preserved 2^-59 witness
//   bun run check:compact    bit network + current compact-control witness
// Options:
//   --verbose                print every row with its source statement
//   --no-observation         skip the B0 observation (the second circuit build; not part of
//                            either verdict), which halves the run time
//   --set=<59|compact>.<parameter>=<p/q>
//                            replace one stated parameter (for example
//                            --set=compact.epsilon=1988/10000) to see the checks
//                            reject it; derived parameters are NOT recomputed
//                            (setting beta leaves C1 as stated, which the guard rows
//                            then reject). May be repeated.
// Exit code 0 only if every counted row of every selected group holds.

import { bitNetwork, paired59, compact, isCounted, type Result } from "./checks";
import { show, toDecimal, div, parseQ, type Q } from "./rational";
import { noteParams, type Params } from "./parameters";
import { compactParams, type CompactParams } from "./compact/witness";

const args = process.argv.slice(2);
const verbose = args.includes("--verbose");
const observation = !args.includes("--no-observation");
const only = args.find((x) => x.startsWith("--only="))?.slice("--only=".length) ?? "all";
if (!["all", "59", "compact"].includes(only)) throw new Error(`unknown --only=${only}`);
for (const a of args)
  if (!(a === "--verbose" || a === "--no-observation" || a.startsWith("--only=") || a.startsWith("--set="))) throw new Error(`unknown argument ${a}`);

const p59: Params = noteParams();
const pc: CompactParams = compactParams();
const overrides: string[] = [];
for (const a of args.filter((x) => x.startsWith("--set="))) {
  const m = /^--set=(59|compact)\.(\w+)=(-?\d+(?:\/\d+)?)$/.exec(a);
  if (!m) throw new Error(`malformed ${a}; expected --set=<59|compact>.<parameter>=<p/q>`);
  const target = (m[1] === "59" ? p59 : pc) as Record<string, Q>;
  if (!(m[2]! in target)) throw new Error(`unknown parameter ${m[2]} for ${m[1]}; known: ${Object.keys(target).join(", ")}`);
  target[m[2]!] = parseQ(m[3]!);
  overrides.push(`${m[1]}.${m[2]} = ${m[3]}`);
}
if (overrides.length) console.log(`PARAMETERS OVERRIDDEN (not the published witness): ${overrides.join("; ")}`);

const t0 = performance.now();
const timings: Record<string, number> = {};
const tick = (label: string, s: number) => (timings[label] = Math.round(performance.now() - s));

const bit = bitNetwork({ tick, alternative: observation });
const groups: { label: string; results: Result[]; summary: string }[] = [];
groups.push({
  label: "bit network (shared)",
  results: bit.results,
  summary: `c = ${bit.values.globalReport.additions}, R = ${bit.values.R}, eta_b = ${show(bit.values.pairedBit.eta)}`,
});
if (only === "all" || only === "59") {
  const r = paired59(bit.values, { tick, p: p59 });
  groups.push({ label: "2^-59 witness (preserved)", results: r.results, summary: `G = ${show(r.values.G)}, kappa = ${show(p59.kappa)}` });
}
if (only === "all" || only === "compact") {
  const r = compact(bit.values, { tick, p: pc });
  groups.push({
    label: "compact-control witness (current)",
    results: r.results,
    summary: `G_* = ${show(r.values.witness.G)}, kappa = ${show(r.values.params.kappa)} (G_*/kappa = ${toDecimal(div(r.values.witness.G, r.values.params.kappa), 6)})`,
  });
}

const TAG: Record<Result["kind"], string> = { check: "ok  ", condition: "ok p", constant: "ok c", sample: "ok s", identity: "id  ", implied: "imp ", observation: "obs " };
let section = "";
for (const g of groups)
  for (const r of g.results) {
    if (r.section !== section) {
      section = r.section;
      console.log(`\n== ${section}`);
    }
    const tag = r.ok ? TAG[r.kind] : isCounted(r) ? "FAIL" : "fail";
    const detail = verbose || !r.ok || r.detail.length <= 70 ? r.detail : "";
    console.log(`${tag} ${r.name}${verbose || !r.ok ? `  [${r.source}]` : ""}  ${detail}`);
  }

const count = (rs: Result[], k: Result["kind"]) => rs.filter((r) => r.kind === k).length;
const seconds = ((performance.now() - t0) / 1000).toFixed(1);
console.log(`\ntimings (ms): ${Object.entries(timings).map(([k, v]) => `${k} ${v}`).join("; ")}`);
console.log(
  `legend: "ok" recomputed check (a value recomputed here, compared with the note); "ok p" parameter condition (a comparison the\n` +
    `        note states between its input parameters; nothing recomputed); "ok c" numeric constant inside a note's argument;\n` +
    `        "ok s" lemma sample (finite instances of a general claim of a note, independent of the witness);\n` +
    `        "id" identity, true for every admissible input (not counted); "imp" same as, or immediate from, counted rows (not counted);\n` +
    `        "obs" observation outside both witnesses (not counted, not in the verdict);\n` +
    `        "FAIL" a counted row fails; "fail" an identity or implied row fails (also fails the run)\n`,
);

const inVerdict = (r: Result) => r.kind !== "observation";
let allOk = true;
for (const g of groups) {
  const failed = g.results.filter((r) => !r.ok && inVerdict(r));
  if (failed.length) allOk = false;
  const obs = g.results.filter((r) => r.kind === "observation");
  console.log(
    `${g.label}: ${count(g.results, "check")} recomputed checks + ${count(g.results, "condition")} parameter conditions + ${count(g.results, "constant")} constants + ${count(g.results, "sample")} lemma samples, ` +
      `${failed.filter(isCounted).length} failed; not counted: ${count(g.results, "identity")} identities, ${count(g.results, "implied")} implied` +
      `${failed.filter((r) => !isCounted(r)).length ? ` (${failed.filter((r) => !isCounted(r)).length} of them FAIL)` : ""}` +
      `${obs.length ? `, ${obs.length} observation (${obs.every((r) => r.ok) ? "holds" : "DOES NOT HOLD"})` : ""}. ${g.summary}`,
  );
}
console.log(`${seconds} s`);
const bitOk = bit.results.every((r) => r.ok || !inVerdict(r));
const verdict = (label: string, ok: boolean) =>
  console.log(`VERDICT ${label}: ${ok ? "PASS" : "FAIL"} (conditional result; recomputed finite checks only; not a formal verification)`);
for (const g of groups.slice(1)) verdict(g.label, bitOk && g.results.every((r) => r.ok || !inVerdict(r)));
for (const g of groups) for (const f of g.results.filter((r) => !r.ok)) console.log(`${inVerdict(f) ? "FAILED" : "OBSERVATION DOES NOT HOLD"}: [${g.label}] ${f.name}: ${f.detail}`);
if (!allOk) process.exit(1);
