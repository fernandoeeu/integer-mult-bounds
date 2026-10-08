// Usage: bun src/main.ts [--h=6,8,...] [--dump=dir]
import { buildPairedCircuit } from "./circuit";
import { verifyLocalCircuit } from "./verifyCircuit";
import { mergeGroups, type Labelling, type KeyMode, tripleList } from "./build";
import { verifyGlobal } from "./verify";
import { checkMatching } from "./matching";
import { writeFileSync, mkdirSync } from "node:fs";

const args = Object.fromEntries(process.argv.slice(2).map((a) => a.replace(/^--/, "").split("=") as [string, string]));
const hs = (args.h ?? "6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50").split(",").map(Number);
const dump = args.dump;
const modes: [Labelling, KeyMode][] = (args.modes ?? "base:support,aligned:support,aligned:star")
  .split(",")
  .map((s) => s.split(":") as [Labelling, KeyMode]);

const BOOL_KEYS = [
  "topo", "disjoint", "common", "exact", "oneMeet", "outputsComplete", "used", "edgeNest",
  "rolePathsNested", "allUsesConsumed", "simRestoresScratch", "simExact",
] as const;

let allOk = true;
for (const h of hs) {
  const t0 = performance.now();
  const local = buildPairedCircuit(h - 1);
  const lr = verifyLocalCircuit(local);
  const localOk = lr.allAdditionsDisjoint && lr.allOutputSupportsExact && lr.everyAdditionUsed;
  if (!localOk) allOk = false;
  console.log(`h=${h} local n=${h - 1}: additions=${lr.additions} outputs=${lr.outputs} nonzero=${lr.nonzeroCoefficients} ok=${localOk}`);
  if (h % 2 === 0 && h >= 6) {
    const m = checkMatching(h);
    const ok = m.bijective && m.intersectionOne && m.joiningLabelsNested;
    if (!ok) allOk = false;
    console.log(`  pi: triples=${m.triples} bijective=${m.bijective} |T cap pi T|=1:${m.intersectionOne} <t_A,t_piA>=0:${m.joiningLabelsNested}`);
  }
  for (const [lab, mode] of modes) {
    if (lab === "aligned" && h % 2 !== 0) continue;
    const G = mergeGroups(local, h, lab, mode);
    const r0 = performance.now();
    const r = verifyGlobal(G, { firstFail: (s) => console.log(`    FAIL ${s}`) });
    const ok = BOOL_KEYS.every((k) => r[k] === true) && r.dupSupports === 0 && r.starMergeMismatches === 0 && r.rolesCompiled === r.rolesCPlusQ;
    if (!ok) allOk = false;
    console.log(
      `  ${lab}/${mode}: c=${r.additions} q=${r.partialOutputs} R=c+q=${r.rolesCPlusQ} compiledRoles=${r.rolesCompiled} merged=${r.mergedAdditions} pruned=${r.prunedAdditions} dupSupports=${r.dupSupports} starMismatch=${r.starMergeMismatches} ` +
        BOOL_KEYS.map((k) => `${k}=${r[k]}`).join(" ") + ` => ${ok ? "PASS" : "FAIL"}`,
    );
    console.log(`    supportSizeSum=${r.supportSizeSum} rssMB=${Math.round(process.memoryUsage().rss / 1048576)} verify ${((performance.now() - r0) / 1000).toFixed(1)} s`);
    if (args.export && h === 50) {
      mkdirSync(args.export, { recursive: true });
      writeFileSync(
        `${args.export}/h${h}-${lab}-${mode}.json`,
        JSON.stringify({ h, left: [...G.left], right: [...G.right], outNode: [...G.outNode], outCommon: [...G.outCommon], outTarget: [...G.outTarget] }),
      );
    }
    if (dump && h <= 14) {
      mkdirSync(dump, { recursive: true });
      writeFileSync(
        `${dump}/h${h}-${lab}-${mode}.json`,
        JSON.stringify({ h, triples: tripleList(h), left: [...G.left], right: [...G.right], outNode: [...G.outNode], outCommon: [...G.outCommon], outTarget: [...G.outTarget] }),
      );
    }
  }
  console.log(`  (${((performance.now() - t0) / 1000).toFixed(1)} s)`);
}
console.log(allOk ? "OVERALL: PASS (no violation)" : "OVERALL: FAIL");
process.exit(allOk ? 0 : 1);
