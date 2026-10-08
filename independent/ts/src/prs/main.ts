// Entry point for the re-check of the outside pull requests (PRs 1 to 4 of 7 October
// 2026 at their pinned heads; PR 4's new head 8c225e6 as "4b", PRs 5 and 6 of 8 October).
//   bun run check:prs                 all seven entries, then cross-PR observations
// Options:
//   --only=1,3,4b                     select PRs (1, 2, 3, 4, 4b, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)
//   --verbose                         print every row with its source
//   --observation                     also build PR 2's and PR 6's aligned graphs under the other
//                                     reading of the circuit prose, count PR 7's global supports a
//                                     second way, and rebuild PR 8's bit screen (not in any verdict)
//   --set=pr<N>.<parameter>=<p/q>     replace one stated parameter of PR N, N in 1..16 (not 11) or 4b (derived
//                                     parameters are NOT recomputed); may be repeated
// Exit code 0 only if every counted row of every selected PR holds.

import { parseQ, type Q } from "../rational";
import { pr1, pr1Params } from "./pr1";
import { pr2, pr2Params } from "./pr2";
import { pr3, pr3Params } from "./pr3";
import { pr4, pr4Params } from "./pr4";
import { pr4b, pr4bParams } from "./pr4b";
import { pr5, pr5Params } from "./pr5";
import { pr6, pr6Params } from "./pr6";
import { pr7, pr7Params } from "./pr7";
import { pr8, pr8Params } from "./pr8";
import { pr9, pr9Params } from "./pr9";
import { pr10, pr10Params } from "./pr10";
import { pr11 } from "./pr11";
import { pr12, pr12Params } from "./pr12";
import { pr13, pr13Params } from "./pr13";
import { pr14, pr14Params } from "./pr14";
import { pr15, pr15Params } from "./pr15";
import { pr16, pr16Params } from "./pr16";
import { cross, cross2, cross3 } from "./cross";
import { counted, type Result } from "./rows";

const args = process.argv.slice(2);
for (const a of args)
  if (!(a === "--verbose" || a === "--observation" || a.startsWith("--only=") || a.startsWith("--set="))) throw new Error(`unknown argument ${a}`);
const verbose = args.includes("--verbose");
const KNOWN = ["1", "2", "3", "4", "4b", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16"];
const only = (args.find((x) => x.startsWith("--only="))?.slice(7) ?? KNOWN.join(",")).split(",");
for (const n of only) if (!KNOWN.includes(n)) throw new Error(`unknown PR ${n}`);

const params: Record<string, Record<string, Q>> = {
  1: pr1Params() as any,
  2: pr2Params() as any,
  3: pr3Params() as any,
  4: pr4Params() as any,
  "4b": pr4bParams() as any,
  5: pr5Params() as any,
  6: pr6Params() as any,
  7: pr7Params() as any,
  8: pr8Params() as any,
  9: pr9Params() as any,
  10: pr10Params() as any,
  12: pr12Params() as any,
  13: pr13Params() as any,
  14: pr14Params() as any,
  15: pr15Params() as any,
  16: pr16Params() as any,
};
const overrides: string[] = [];
for (const a of args.filter((x) => x.startsWith("--set="))) {
  const m = /^--set=pr(4b|1[0-6]|[1-9])\.(\w+)=(-?\d+(?:\/\d+)?)$/.exec(a);
  if (!m) throw new Error(`malformed ${a}; expected --set=pr<N>.<parameter>=<p/q>`);
  const target = params[m[1]!];
  if (!target) throw new Error(`PR ${m[1]} has no parameters to set`);
  if (!(m[2]! in target)) throw new Error(`unknown parameter ${m[2]} for PR ${m[1]}; known: ${Object.keys(target).join(", ")}`);
  target[m[2]!] = parseQ(m[3]!);
  overrides.push(`pr${m[1]}.${m[2]} = ${m[3]}`);
}
if (overrides.length) console.log(`PARAMETERS OVERRIDDEN (not the PRs' witnesses): ${overrides.join("; ")}`);

const t0 = performance.now();
const groups: { label: string; results: Result[] }[] = [];
const time: string[] = [];
const run = (label: string, f: () => Result[]) => {
  const s = performance.now();
  groups.push({ label, results: f() });
  time.push(`${label.split(" ")[0]} ${((performance.now() - s) / 1000).toFixed(1)} s`);
};
if (only.includes("1")) run("PR1 (Prosz, tuned paired parameters, kappa = 17523184/10^25)", () => pr1({ p: params[1] as any }).results);
if (only.includes("2")) run("PR2 (Barnes, aligned paired circuit, kappa = 17*2^-63)", () => pr2({ p: params[2] as any, alternative: args.includes("--observation") }).results);
if (only.includes("3")) run("PR3 (eumemic, compressed complex circuit, kappa = 59/10^11)", () => pr3({ p: params[3] as any }).results);
if (only.includes("4")) run("PR4 (Leen, retained complex totals, kappa = 591/10^12)", () => pr4({ p: params[4] as any }).results);
if (only.includes("4b")) run("PR4b (Leen, head 8c225e6: PR 3 circuit + retained totals, a_c = 2970/10^11, kappa = 591/10^12)", () => pr4b({ p: params["4b"] as any }).results);
if (only.includes("5")) run("PR5 (eumemic, fast Gaussian resampling, kappa = 1479/10^12)", () => pr5({ p: params[5] as any }).results);
if (only.includes("6")) run("PR6 (eumemic, aligned bit circuit with cheaper centers, kappa = 1624/10^12)", () => pr6({ p: params[6] as any, alternative: args.includes("--observation") }).results);
if (only.includes("7")) run("PR7 (jacklightChen, F3 five-subset bit network + paired complex producer, kappa = 373/10^11)", () => pr7({ p: params[7] as any, observation: args.includes("--observation") }).results);
if (only.includes("8")) run("PR8 (Rohan Arun, geometric complex-network candidate, kappa = 59/10^11)", () => pr8({ p: params[8] as any, observation: args.includes("--observation") }).results);
if (only.includes("9")) run("PR9 (Rohan Arun, refined ternary star templates, kappa = 19/(5*10^9))", () => pr9({ p: params[9] as any }).results);
if (only.includes("10")) run("PR10 (icekylinx, batched recursive networks, kappa = 6149999/(5*10^13))", () => pr10({ p: params[10] as any }).results);
if (only.includes("11")) run("PR11 (Rohan Arun, geometric dimension screen and matching; no new exponent)", () => pr11().results);
if (only.includes("12")) run("PR12 (Rohan Arun, h = 30 bit network with controlled batching, kappa = 12649/10^11)", () => pr12({ p: params[12] as any }).results);
if (only.includes("13")) run("PR13 (eumemic, auxiliary source frames, kappa = 7699/10^10)", () => pr13({ p: params[13] as any }).results);
if (only.includes("14")) run("PR14 (Rohan Arun, source frames + h = 30 data corners, kappa = 90799/10^11)", () => pr14({ p: params[14] as any }).results);
if (only.includes("15")) run("PR15 (eumemic, smaller h = 30 source-frame network + all complex residuals, kappa = 1076678/10^12)", () => pr15({ p: params[15] as any }).results);
if (only.includes("16")) run("PR16 (jacklightChen, nested source-frame batching at h = 32, kappa = 9799/10^10)", () => pr16({ p: params[16] as any }).results);
if (["1", "2", "3", "4"].every((n) => only.includes(n))) run("X (cross-PR speculation)", cross);
if (["4b", "5", "6"].every((n) => only.includes(n))) run("X2 (cross-PR speculation, PRs 4b to 6)", cross2);
if (["14", "15", "16"].every((n) => only.includes(n))) run("X3 (cross-PR observations and speculation, PRs 14 to 16)", cross3);

const TAG: Record<Result["kind"], string> = { check: "ok  ", condition: "ok p", constant: "ok c", sample: "ok s", identity: "id  ", implied: "imp ", observation: "obs " };
let section = "";
for (const g of groups)
  for (const r of g.results) {
    if (r.section !== section) {
      section = r.section;
      console.log(`\n== ${section}`);
    }
    const tag = r.ok ? TAG[r.kind] : r.kind === "observation" ? "obs!" : counted(r) ? "FAIL" : "fail";
    const detail = verbose || !r.ok || r.detail.length <= 70 || r.kind === "observation" ? r.detail : "";
    console.log(`${tag} ${r.name}${verbose || (!r.ok && r.kind !== "observation") ? `  [${r.source}]` : ""}  ${detail}`);
  }

console.log(`\ntimings: ${time.join("; ")}`);
console.log(
  `legend: "ok" recomputed check; "ok p" parameter condition; "ok c" constant; "id" identity (not counted); "imp" implied (not counted);\n` +
    `        "obs" observation or speculation (not counted, not in any verdict; "obs!" = the observed statement is false);\n` +
    `        "FAIL" a counted row fails; "fail" an identity or implied row fails (also fails the PR)`,
);
const n = (rs: Result[], k: Result["kind"]) => rs.filter((r) => r.kind === k).length;
let allOk = true;
for (const g of groups.filter((g) => g.label.startsWith("PR"))) {
  const failed = g.results.filter((r) => !r.ok && r.kind !== "observation");
  if (failed.length) allOk = false;
  console.log(
    `${g.label}: ${n(g.results, "check")} recomputed checks + ${n(g.results, "condition")} parameter conditions + ${n(g.results, "constant")} constants, ` +
      `${failed.filter(counted).length} failed; not counted: ${n(g.results, "identity")} identities, ${n(g.results, "implied")} implied, ${n(g.results, "observation")} observations`,
  );
}
console.log(`${((performance.now() - t0) / 1000).toFixed(1)} s`);
for (const g of groups.filter((g) => g.label.startsWith("PR"))) {
  const ok = g.results.every((r) => r.ok || r.kind === "observation");
  console.log(`VERDICT ${g.label.split(" ")[0]}: ${ok ? "PASS" : "FAIL"} (finite arithmetic and counts only; the PR remains conditional; not a formal verification)`);
}
for (const g of groups) for (const f of g.results.filter((r) => !r.ok && r.kind !== "observation")) console.log(`FAILED: [${g.label.split(" ")[0]}] ${f.name}: ${f.detail}`);
// Errata: sentences of a PR's text whose numbers disagree with its own fixed parameters. They are
// observations (the witness does not use them), printed here so that they are not missed.
for (const g of groups) for (const f of g.results.filter((r) => !r.ok && r.kind === "observation" && r.name.startsWith("ERRATUM"))) console.log(`ERRATUM: [${g.label.split(" ")[0]}] ${f.name.slice(8)}: ${f.detail}`);
if (!allOk) process.exit(1);
