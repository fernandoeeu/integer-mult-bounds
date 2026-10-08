// PR 4 (David Leen): the counts of the retained-total complex producer at h = 24,
// recomputed from notes/retained-complex-construction.tex ("Side correction by
// shared source trees", "Retained roots and doubled totals", "Exact counts and
// recurrence").
//
// Disjoint branch. The note: "recursively partition ordered disjoint triple pairs
// into rectangles. On D(a,b), use a row-star partition, a column-star partition,
// or split the ground set and partition each source/target cardinality case by
// the product of its two smaller disjointness partitions. [...] For a rectangle
// with a source triples and b targets [...] It costs a+b-1 roles." The selected
// plan is the cheapest one in that family. The note does not say where the ground
// set is split or how ties are broken. Here every split point is tried, the first
// candidate (rows, columns, then splits by increasing size of the first part) is
// kept on ties, and the role count of the root is also recomputed with the LAST
// minimal candidate kept on ties, to see whether ties matter.
// Caveat: scripts/retained_complex.py (best_plan) was read before this was written;
// the candidate order and the base cases agree with it.
//
// Repair: "If its full source union is the complete complement of any target,
// split that rectangle into singleton-edge rectangles [...] Every repaired
// rectangle in the selected h=24 plan has one target, so this repair preserves
// its role count. The repaired disjoint branch costs 329811 roles, with 123855
// additions and 205956 outputs."

import { binom } from "../intmath";
import { tripleIndex, tripleList } from "../global";

export type Plan = {
  n: number;
  a: number;
  b: number;
  count: bigint; // rectangles
  src: bigint; // sum of source family sizes
  tgt: bigint; // sum of target family sizes
  kind: "empty" | "base" | "rows" | "cols" | "split";
  split?: number;
  terms?: [Plan, Plan][];
};
export const roles = (p: Plan) => p.src + p.tgt - p.count; // sum of (a + b - 1)

export type TieRule = "first" | "last";

export function bestPlan(n: number, a: number, b: number, tie: TieRule = "first", memo = new Map<string, Plan>()): Plan {
  const key = `${n},${a},${b}`;
  const m = memo.get(key);
  if (m) return m;
  let plan: Plan;
  if (a < 0 || b < 0 || a + b > n) plan = { n, a, b, count: 0n, src: 0n, tgt: 0n, kind: "empty" };
  else if (a === 0 || b === 0) plan = { n, a, b, count: 1n, src: binom(n, a), tgt: binom(n, b), kind: "base" };
  else {
    const ca = binom(n, a);
    const cb = binom(n, b);
    const cands: Plan[] = [
      { n, a, b, count: ca, src: ca, tgt: ca * binom(n - a, b), kind: "rows" },
      { n, a, b, count: cb, src: cb * binom(n - b, a), tgt: cb, kind: "cols" },
    ];
    for (let s = 1; s < n; s++) {
      const terms: [Plan, Plan][] = [];
      for (let x = 0; x <= a; x++)
        for (let y = 0; y <= b; y++) {
          if (x + y > s || a - x + (b - y) > n - s) continue;
          const L = bestPlan(s, x, y, tie, memo);
          const R = bestPlan(n - s, a - x, b - y, tie, memo);
          if (L.count && R.count) terms.push([L, R]);
        }
      if (!terms.length) continue;
      cands.push({
        n,
        a,
        b,
        count: terms.reduce((t, [L, R]) => t + L.count * R.count, 0n),
        src: terms.reduce((t, [L, R]) => t + L.src * R.src, 0n),
        tgt: terms.reduce((t, [L, R]) => t + L.tgt * R.tgt, 0n),
        kind: "split",
        split: s,
        terms,
      });
    }
    plan = cands[0]!;
    for (const c of cands.slice(1)) if (roles(c) < roles(plan) || (tie === "last" && roles(c) === roles(plan))) plan = c;
  }
  memo.set(key, plan);
  return plan;
}

type Rect = { src: number[][]; tgt: number[][] };

/** The rectangles of a plan on an ordered point list (left part = first `split` points). */
export function* rectangles(p: Plan, points: number[]): Generator<Rect> {
  const combos = (pts: number[], k: number): number[][] => {
    const out: number[][] = [];
    const rec = (i: number, cur: number[]) => {
      if (cur.length === k) return void out.push([...cur]);
      for (let j = i; j < pts.length; j++) rec(j + 1, [...cur, pts[j]!]);
    };
    rec(0, []);
    return out;
  };
  if (p.kind === "empty") return;
  if (p.kind === "base") yield { src: combos(points, p.a), tgt: combos(points, p.b) };
  else if (p.kind === "rows")
    for (const s of combos(points, p.a)) yield { src: [s], tgt: combos(points.filter((x) => !s.includes(x)), p.b) };
  else if (p.kind === "cols")
    for (const t of combos(points, p.b)) yield { src: combos(points.filter((x) => !t.includes(x)), p.a), tgt: [t] };
  else {
    const Lp = points.slice(0, p.split!);
    const Rp = points.slice(p.split!);
    for (const [L, R] of p.terms!)
      for (const l of rectangles(L, Lp))
        for (const r of rectangles(R, Rp))
          yield {
            src: l.src.flatMap((x) => r.src.map((y) => [...x, ...y])),
            tgt: l.tgt.flatMap((x) => r.tgt.map((y) => [...x, ...y])),
          };
  }
}

export type DisjointReport = {
  rawRectangles: number;
  rawRoles: bigint;
  exactPartition: boolean; // every disjoint (source, target) pair of triples exactly once, nothing else
  pairsCovered: number;
  badRectangles: number;
  badWithOneTarget: number;
  repairedRectangles: number;
  additions: number; // sum (a - 1) after repair
  outputs: number; // sum b after repair
  roles: number;
  duplicateSourceFamilies: number; // rectangles whose source family already occurred (observation)
  duplicateAdditions: number; // additions those rectangles spend on a source tree that already exists
};

/** Enumerate the plan's rectangles at ground size h, check the partition, apply the repair, count. */
export function disjointBranch(h: number, plan: Plan): DisjointReport {
  const tl = tripleList(h);
  const V = tl.length;
  const full = (1 << h) - 1;
  const mask = (t: number[]) => t.reduce((m, p) => m | (1 << p), 0);
  const seen = new Uint8Array(V * V);
  let exact = true;
  let covered = 0;
  let raw = 0;
  let rawRoles = 0n;
  let bad = 0;
  let badOne = 0;
  let rects = 0;
  let additions = 0;
  let outputs = 0;
  const families = new Set<string>();
  let dup = 0;
  let dupAdd = 0;
  for (const r of rectangles(plan, [...Array(h).keys()])) {
    raw++;
    rawRoles += BigInt(r.src.length + r.tgt.length - 1);
    let union = 0;
    for (const s of r.src) union |= mask(s);
    for (const s of r.src)
      for (const t of r.tgt) {
        if ((mask(s) & mask(t)) !== 0) exact = false;
        const k = tripleIndex(h, s) * V + tripleIndex(h, t);
        if (seen[k]) exact = false;
        seen[k] = 1;
        covered++;
      }
    const isBad = r.tgt.some((t) => union === (full ^ mask(t)));
    if (isBad) {
      bad++;
      if (r.tgt.length === 1) badOne++;
      // split into singleton-edge rectangles: |src||tgt| rectangles with one source and one target
      rects += r.src.length * r.tgt.length;
      outputs += r.src.length * r.tgt.length;
    } else {
      rects++;
      additions += r.src.length - 1;
      outputs += r.tgt.length;
      const key = r.src.map((s) => tripleIndex(h, s)).sort((x, y) => x - y).join(",");
      if (r.src.length > 1) {
        if (families.has(key)) {
          dup++;
          dupAdd += r.src.length - 1;
        }
        families.add(key);
      }
    }
  }
  // every disjoint pair must be covered: count them
  let disjointPairs = 0;
  for (const s of tl) for (const t of tl) if ((mask(s) & mask(t)) === 0) disjointPairs++;
  if (covered !== disjointPairs) exact = false;
  return { rawRectangles: raw, rawRoles, exactPartition: exact, pairsCovered: covered, badRectangles: bad, badWithOneTarget: badOne, repairedRectangles: rects, additions, outputs, roles: additions + outputs, duplicateSourceFamilies: dup, duplicateAdditions: dupAdd };
}

/**
 * Fixed-pair trees: a balanced tree on the n = h - 2 variables of a pair (split at
 * floor or ceil); for target P + {r} the maximal subtrees avoiding r are the
 * siblings on the path from leaf r to the root. Returns the number of selected
 * outputs (sum of leaf depths), the note's formula n(n-1) - sum over internal
 * nodes of (n - |K|), the number of additions, and whether every selected subtree
 * leaves a spare point beyond r (|K| + 1 < n).
 */
export function pairTree(n: number, split: "floor" | "ceil" = "floor") {
  let depthSum = 0;
  let internalSum = 0;
  let additions = 0;
  let spare = true;
  // returns the leaf count; walks with the current depth
  const walk = (size: number, depth: number) => {
    if (size === 1) {
      depthSum += depth;
      return;
    }
    additions++;
    internalSum += n - size;
    const l = split === "floor" ? size >> 1 : (size + 1) >> 1;
    // a selected subtree is a child whose sibling contains r: it has l or size - l leaves
    if (l + 1 >= n || size - l + 1 >= n) spare = false;
    walk(l, depth + 1);
    walk(size - l, depth + 1);
  };
  walk(n, 0);
  return { outputs: depthSum, formula: n * (n - 1) - internalSum, additions, spare };
}
