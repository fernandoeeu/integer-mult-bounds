// PR 9 (Rohan Arun): alternative greedy rules for PR 7's four-point star templates.
// Rule, from research/prime-field-followup/README.md ("favors the largest union support
// when the frequency is tied ... ascending and descending union masks ... prunes unused
// addition ancestors ... retains the smallest circuit for each canonical template"); the
// exact tie order (frequency, then larger union size, then union mask ascending or
// descending, then the operand pair ascending) and the three candidates {PR 7's published
// greedy, large-first, large-first with descending masks} were read from
// star_duality.py / verify.py (see the independence caveats in prs/REPORT.md).

const pop32 = (x: number) => {
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
};

/** The large-first greedy (descending masks if `reverse`), followed by pruning of gates no output needs. */
export function largeFirstGreedy(masks: number[], reverse: boolean): [number, number][] {
  let width = 0;
  for (const m of masks) width = Math.max(width, 32 - Math.clz32(m));
  const computed = new Set<number>();
  for (let i = 0; i < width; i++) computed.add(2 ** i);
  const terms: Set<number>[] = masks.map((m) => {
    const t = new Set<number>();
    for (let i = 0; i < width; i++) if ((m >>> i) & 1) t.add(2 ** i);
    return t;
  });
  const gates: [number, number][] = [];
  const K = 33554432; // operands < 2^25
  while (terms.some((t) => t.size > 1)) {
    const freq = new Map<number, number>();
    for (const t of terms) {
      const s = [...t].sort((x, y) => x - y);
      for (let i = 0; i < s.length; i++) for (let j = i + 1; j < s.length; j++) {
        const k = s[i]! * K + s[j]!;
        freq.set(k, (freq.get(k) ?? 0) + 1);
      }
    }
    let best = -1;
    let bf = 0;
    let bc = 0;
    let bu = 0;
    for (const [k, f] of freq) {
      const a = Math.floor(k / K);
      const b = k - a * K;
      const u = (a | b) >>> 0;
      const c = pop32(u);
      const better =
        best < 0 ||
        f > bf ||
        (f === bf && (c > bc || (c === bc && ((reverse ? u > bu : u < bu) || (u === bu && k < best)))));
      if (better) {
        best = k;
        bf = f;
        bc = c;
        bu = u;
      }
    }
    const a = Math.floor(best / K);
    const b = best - a * K;
    if ((a & b) !== 0) throw new Error("joined overlapping terms");
    const value = (a | b) >>> 0;
    if (!computed.has(value)) {
      if (!(computed.has(a) && computed.has(b))) throw new Error("operand not available");
      gates.push([a, b]);
      computed.add(value);
    }
    for (const t of terms) {
      const contained = [...t].filter((x) => (x & ~value) === 0);
      if (contained.length > 1 && contained.reduce((s, x) => s + x, 0) === value) {
        for (const x of contained) t.delete(x);
        t.add(value);
      }
    }
  }
  terms.forEach((t, i) => {
    if (t.size !== 1 || [...t][0] !== masks[i]) throw new Error("a requested sum was not produced");
  });
  return pruneGates(gates, masks);
}

/** Keep only gates on which some requested sum depends. */
export function pruneGates(gates: [number, number][], outputs: number[]): [number, number][] {
  const parent = new Map<number, [number, number]>();
  for (const [a, b] of gates) parent.set((a | b) >>> 0, [a, b]);
  const needed = new Set<number>();
  const stack = [...outputs];
  while (stack.length) {
    const x = stack.pop()!;
    if (needed.has(x)) continue;
    needed.add(x);
    const p = parent.get(x);
    if (p) stack.push(p[0], p[1]);
  }
  return gates.filter(([a, b]) => needed.has((a | b) >>> 0));
}
