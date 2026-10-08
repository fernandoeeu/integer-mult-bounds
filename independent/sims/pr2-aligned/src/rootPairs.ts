// Literal check of "All complete root pairs now agree across groups."
// The local recursion's root blocks are local vertices {0,1},{2,3},...,{n-2,n-1}
// with final singleton n-1 when n is odd (n = h-1 is odd for even h).
// Under each labelling, map the root blocks of group i to ground pairs and ask:
//  (a) is every complete root block a global pair {2t, 2t+1}?
//  (b) does every unordered ground pair that is a complete root block in some
//      group occur as a complete root block in every group whose common point
//      is outside it?
import { labelOf, type Labelling } from "./build";

let ok = true;
for (const h of [6, 8, 10, 12, 20, 30, 40, 50]) {
  for (const kind of ["base", "aligned"] as Labelling[]) {
    const n = h - 1;
    const blocks: Set<string>[] = [];
    let allGlobal = true;
    let singletons: number[] = [];
    for (let i = 0; i < h; i++) {
      const lab = labelOf(h, i, kind);
      const s = new Set<string>();
      for (let u = 0; u + 1 < n; u += 2) {
        const a = Math.min(lab[u]!, lab[u + 1]!), b = Math.max(lab[u]!, lab[u + 1]!);
        s.add(`${a},${b}`);
        if (!(a % 2 === 0 && b === a + 1)) allGlobal = false;
      }
      if (n % 2 === 1) singletons.push(lab[n - 1]!);
      blocks.push(s);
    }
    const union = new Set<string>();
    blocks.forEach((s) => s.forEach((k) => union.add(k)));
    let agree = true;
    for (const k of union) {
      const [a, b] = k.split(",").map(Number) as [number, number];
      for (let i = 0; i < h; i++) if (i !== a && i !== b && !blocks[i]!.has(k)) agree = false;
    }
    const singletonIsPartner = singletons.every((x, i) => x === (i ^ 1));
    console.log(`h=${h} ${kind}: completeRootBlocksAreGlobalPairs=${allGlobal} rootPairsAgreeAcrossGroups=${agree} singletonIsPartner=${singletonIsPartner}`);
    if (kind === "aligned" && !(allGlobal && agree && singletonIsPartner)) ok = false;
  }
}
console.log(ok ? "ROOT PAIRS: PASS" : "ROOT PAIRS: FAIL");
process.exit(ok ? 0 : 1);
