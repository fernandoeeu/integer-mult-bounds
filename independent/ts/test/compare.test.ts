// `bun run compare` must report a disagreement when the certificate disagrees, and must
// refuse to report when a certificate field is not classified exactly once.
import { describe, expect, test } from "bun:test";
import { compare59, compareCompact, readCert } from "../src/compare";
import { Comparator } from "../src/comparator";
import { q } from "../src/rational";
import { bitValues } from "./shared";

/** A deep copy of a certificate with one dotted path replaced (or deleted when value is undefined). */
function edit(cert: unknown, path: string[], value: unknown): unknown {
  const copy = structuredClone(cert) as Record<string, any>;
  let o = copy;
  for (const k of path.slice(0, -1)) o = o[k];
  if (value === undefined) delete o[path.at(-1)!];
  else o[path.at(-1)!] = value;
  return copy;
}

describe("Comparator", () => {
  test("statuses: equal value -> recomputed, different value -> DIFFER, unlisted field -> refuses", () => {
    const C = new Comparator("t", { a: "3/4", b: "7", c: "x" });
    C.recomputed("a", q(3n, 4n));
    C.recomputed("b", 8n);
    expect(() => C.finish(false)).toThrow(/unclassified fields c/);
    C.skip("c", "descriptive");
    const r = C.finish(false);
    expect([r.recomputed, r.DIFFER, r["not compared"], r.leaves]).toEqual([1, 1, 1, 3]);
  });
  test("a field listed twice, or a field that does not exist, is refused", () => {
    const C = new Comparator("t", { a: "1" });
    C.input("a", 1n);
    expect(() => C.input("a", 1n)).toThrow(/listed twice/);
    expect(() => C.recomputed("b", 1n)).toThrow(/no certificate field/);
  });
});

describe("compare with the real certificates", () => {
  test("paired-network.json: no disagreement; totals cover every leaf field", async () => {
    const r = await compare59(bitValues(), { print: false });
    expect(r.DIFFER).toBe(0);
    expect(r.leaves).toBe(r.leafCounts.recomputed + r.leafCounts["recomputed*"] + r.leafCounts.input + r.leafCounts["other method"] + r.leafCounts["not compared"]);
  }, 60_000);
  test("compact-control-layer.json: no disagreement; totals cover every leaf field", async () => {
    const r = await compareCompact({ print: false });
    expect(r.DIFFER).toBe(0);
    expect(r.leaves).toBe(r.leafCounts.recomputed + r.leafCounts["recomputed*"] + r.leafCounts.input + r.leafCounts["other method"] + r.leafCounts["not compared"]);
  }, 60_000);
});

describe("compare rejects corrupted certificates", () => {
  test("paired-network.json with W_b changed by one, or with forward frames false, gives DIFFER", async () => {
    const cert = await readCert("paired-network.json");
    const W = (cert as any).bit_counts.W as string;
    expect((await compare59(bitValues(), { cert: edit(cert, ["bit_counts", "W"], String(BigInt(W) + 1n)), print: false })).DIFFER).toBe(1);
    expect((await compare59(bitValues(), { cert: edit(cert, ["frames", "forward_frames_nested"], false), print: false })).DIFFER).toBe(1);
    expect((await compare59(bitValues(), { cert: edit(cert, ["global_circuit", "additions"], "450244"), print: false })).DIFFER).toBe(1);
  }, 60_000);
  test("paired-network.json with an extra or a missing field is refused", async () => {
    const cert = await readCert("paired-network.json");
    expect(compare59(bitValues(), { cert: edit(cert, ["bit_counts", "extra"], "1"), print: false })).rejects.toThrow(/unclassified/);
    expect(compare59(bitValues(), { cert: edit(cert, ["bit_counts", "W"], undefined), print: false })).rejects.toThrow(/no certificate field/);
  }, 60_000);
  test("compact-control-layer.json: a changed margin, a changed scoped ceiling and a changed source hash each give DIFFER", async () => {
    const cert = await readCert("compact-control-layer.json");
    expect((await compareCompact({ cert: edit(cert, ["main", "margins", "g3"], "333834/4000000000000000"), print: false })).DIFFER).toBe(1);
    // an upper enclosure below the true a*/5 contradicts the TypeScript lower bound
    expect((await compareCompact({ cert: edit(cert, ["scoped_ceiling", "upper"], "8369/100000000000000"), print: false })).DIFFER).toBe(1);
    const hashes = (cert as any).proof_sha256 as Record<string, string>;
    const key = Object.keys(hashes)[0]!;
    expect((await compareCompact({ cert: edit(cert, ["proof_sha256", key], "0".repeat(64)), print: false })).DIFFER).toBe(1);
  }, 60_000);
  test("compact-control-layer.json: a milestone whose kappa exceeds its own margin is reported", async () => {
    const cert = await readCert("compact-control-layer.json");
    const r = await compareCompact({ cert: edit(cert, ["milestones", "target_34", "parameters", "kappa"], "1/100"), print: false });
    expect(r.extra.some((e) => e.startsWith("target_34") && e.includes("FAIL"))).toBe(true);
    expect(r.DIFFER).toBeGreaterThan(0);
  }, 60_000);
});
