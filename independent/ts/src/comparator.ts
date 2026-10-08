// Field-by-field comparison of recomputed values with a JSON certificate.
//
// Every row has one status:
//   recomputed        the TypeScript value, recomputed from the note's inputs, equals the certificate value exactly;
//   recomputed*       the same, but the instance's inputs (for example d, D, K, G or a milestone's parameters)
//                     were read from the certificate because the note does not state them;
//   input             the certificate value is an input of the note (or follows from inputs by a fixed
//                     allocation, such as C(49,2) input nodes); equality only shows that the same inputs were used;
//   other method      the TypeScript establishes the same claim by a DIFFERENT method (a different enclosure
//                     of the same real number, or a support-level argument instead of a per-role check);
//                     the row records that the conclusions agree, not that the same computation was repeated;
//   DIFFER            both exist and disagree (always investigated, never adjusted);
//   not compared      with the reason (descriptive strings, hashes of the Python's encoding, inputs of
//                     instances read from the certificate).
//
// finish() flattens the certificate and refuses to report unless every leaf
// field is covered by exactly one row. A row may cover a whole array (for
// example limiting_margins = ["g2","g3"]); totals are reported both as rows and
// as leaf fields.

import { type Q, show, parseQ, eq } from "./rational";

export type Status = "recomputed" | "recomputed*" | "input" | "other method" | "DIFFER" | "not compared";
type Row = { field: string; status: Status; ts: string; cert: string };

/**
 * JSON.parse without precision loss: certificates/compact-control-layer.json stores
 * integers of up to 118 digits as bare JSON numbers, which JSON.parse would round to
 * doubles. Every bare number outside a string is first wrapped in quotes; a
 * non-integer number is rejected (none occurs in the certificates).
 */
export function parseLossless(text: string): unknown {
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
      const lit = text.slice(i, j);
      if (!/^-?\d+$/.test(lit)) throw new Error(`non-integer number ${lit} in certificate`);
      out += `"${lit}"`;
      i = j - 1;
      continue;
    }
    out += ch;
  }
  return JSON.parse(out);
}

const isQ = (x: unknown): x is Q => typeof x === "object" && x !== null && "num" in x && "den" in x;
const fmt = (x: unknown) => (isQ(x) ? show(x) : String(x));

export class Comparator {
  rows: Row[] = [];
  constructor(
    readonly label: string,
    readonly cert: unknown,
  ) {}

  /** Value at a dotted path; a key may itself contain dots (e.g. "proof_sha256.notes/x.tex"). */
  get(path: string): unknown {
    const walk = (o: unknown, rest: string): unknown => {
      if (o === null || typeof o !== "object") return undefined;
      const rec = o as Record<string, unknown>;
      if (Object.hasOwn(rec, rest)) return rec[rest];
      for (const k of Object.keys(rec)) if (rest.startsWith(k + ".")) return walk(rec[k], rest.slice(k.length + 1));
      return undefined;
    };
    return walk(this.cert, path);
  }

  private has(path: string) {
    return this.get(path) !== undefined;
  }

  private agree(path: string, ts: unknown): boolean {
    const c = this.get(path);
    const numeric = typeof c === "string" && /^-?\d+(\/\d+)?$/.test(c);
    if (isQ(ts)) return numeric && eq(parseQ(c as string), ts);
    if (typeof ts === "bigint" || typeof ts === "number") return numeric && !(c as string).includes("/") && BigInt(c as string) === BigInt(ts);
    if (Array.isArray(c)) return c.join(",") === String(ts); // a list of labels, compared element-wise
    return typeof c !== "object" && String(c) === String(ts);
  }

  private push(field: string, status: Status, ts: string) {
    if (!this.has(field)) throw new Error(`${this.label}: no certificate field ${field}`);
    if (this.rows.some((r) => r.field === field)) throw new Error(`${this.label}: field ${field} listed twice`);
    this.rows.push({ field, status, ts, cert: JSON.stringify(this.get(field)) ?? "" });
  }

  recomputed(path: string, ts: unknown, certInputs = false) {
    this.push(path, this.agree(path, ts) ? (certInputs ? "recomputed*" : "recomputed") : "DIFFER", fmt(ts));
  }
  input(path: string, ts: unknown) {
    this.push(path, this.agree(path, ts) ? "input" : "DIFFER", fmt(ts));
  }
  /** Same claim, different method: `ok` says the two conclusions agree. */
  otherMethod(path: string, ok: boolean, detail: string) {
    this.push(path, ok ? "other method" : "DIFFER", detail);
  }
  skip(path: string, why: string) {
    this.push(path, "not compared", why);
  }

  /** All leaf paths of the certificate. Arrays are indexed (".0", ".1", ...). */
  leaves(): string[] {
    const out: string[] = [];
    const walk = (o: unknown, p: string) => {
      if (Array.isArray(o)) o.forEach((v, i) => walk(v, `${p}.${i}`));
      else if (o !== null && typeof o === "object") for (const [k, v] of Object.entries(o)) walk(v, p ? `${p}.${k}` : k);
      else out.push(p);
    };
    walk(this.cert, "");
    return out;
  }

  /** Verify full coverage and print. Returns the counts. */
  finish(print = true) {
    const covered = (leaf: string) => this.rows.filter((r) => leaf === r.field || leaf.startsWith(r.field + ".")).length;
    const unlisted = this.leaves().filter((l) => covered(l) === 0);
    const doubly = this.leaves().filter((l) => covered(l) > 1);
    if (unlisted.length || doubly.length)
      throw new Error(`${this.label}: unclassified fields ${unlisted.join(", ")}; doubly classified ${doubly.join(", ")}`);
    const counts: Record<Status, number> = { recomputed: 0, "recomputed*": 0, input: 0, "other method": 0, DIFFER: 0, "not compared": 0 };
    const leafCounts: Record<Status, number> = { ...counts };
    const leaves = this.leaves();
    for (const r of this.rows) {
      counts[r.status]++;
      leafCounts[r.status] += leaves.filter((l) => l === r.field || l.startsWith(r.field + ".")).length;
    }
    if (print) {
      const width = Math.max(...this.rows.map((r) => r.field.length));
      console.log(`\n=== ${this.label}`);
      for (const r of this.rows) {
        const tail = r.status === "DIFFER" ? `ts=${r.ts.slice(0, 90)}  cert=${r.cert.slice(0, 90)}` : r.ts.slice(0, 70);
        console.log(`${r.status.padEnd(13)} ${r.field.padEnd(width)}  ${tail}`);
      }
      const line = (c: Record<Status, number>) =>
        `${c.recomputed} recomputed and agreeing, ${c["recomputed*"]} recomputed from instance inputs read from the certificate, ` +
        `${c.input} inputs, ${c["other method"]} established by a different method, ${c.DIFFER} differ, ${c["not compared"]} not compared`;
      console.log(`\n${this.label}`);
      console.log(`  rows (${this.rows.length}):        ${line(counts)}`);
      console.log(`  leaf fields (${leaves.length}): ${line(leafCounts)}`);
    }
    return { ...counts, rows: this.rows.length, leaves: leaves.length, leafCounts };
  }
}
