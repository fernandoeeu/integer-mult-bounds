// PR 7 (jacklightChen): the global producer of the F3 five-subset bit network,
// rebuilt from notes/prime-field28-construction.tex, paragraphs "Cancellation-free
// triple exclusion" (last two sentences), the global identification paragraphs and
// "Resynthesizing four-point stars".
//
// Top-down.
//   * Ground set [h], h even, paired {0,1},{2,3},...; inputs x_T for the five-sets T.
//   * For every common pair C (C(h,2) contexts) one copy of the local producer on the
//     n = h - 2 other points (src/prs/pairedTriple.ts): local point i stands for
//     order_C[i], where order_C lists the intact global pairs first and then the
//     partners of the points of C ("order the intact global pairs first and place the
//     partners of its removed points last"). A local triple U stands for C cup U.
//     Outputs per context: the 2600 sums D_{C,E} and the retained total A_C, so
//     q = C(h-2,3) C(h,2) + C(h,2) = 10 v + C(h,2) at h = 28.
//   * "Identify equal source supports across these local producers, retaining an
//     existing decomposition, then remove unused ancestors." A sum whose five-sets
//     share exactly C belongs to context C only; a sum whose five-sets share a
//     3-set K is keyed by K and its set of remaining pairs; a 4-set B by B and its
//     set of remaining points. Contexts are processed in lexicographic order of C
//     and local nodes in creation order (the order is not stated in the note; it is
//     the order of the PR's checker and decides only which decomposition is kept).
//   * Stars: for every 4-set B, the additions whose five-sets all contain B form the
//     star of B. The requested sums of a star are its nodes used by an addition
//     outside the star or designated as outputs. Each star is replaced by the greedy
//     disjoint common-subexpression circuit `greedyCSE` for exactly those sums, after
//     relabelling the 24 remaining points canonically (intact global pairs first, then
//     the partners of B's points). Equal relabelled request lists share a template.
//
// The keys here are exact (bit sets, not fingerprints). `fingerprintCount` is a
// second, probabilistic route to the number of distinct supports (128-bit additive
// fingerprints of the five-set sets), used as a cross-check.

import { type ActiveGraph, verifyPairedTriple } from "./pairedTriple";

const pop32 = (x: number) => {
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
};
const ctz = (x: number) => 31 - Math.clz32(x & -x);

/** colex rank of a k-subset given as a bit mask, plus one (ids 1..C(h,k)). */
function makeRank(h: number) {
  const C: number[][] = Array.from({ length: h + 1 }, () => new Array(7).fill(0));
  for (let n = 0; n <= h; n++) {
    C[n]![0] = 1;
    for (let k = 1; k <= 6; k++) C[n]![k] = n === 0 ? 0 : C[n - 1]![k - 1]! + C[n - 1]![k]!;
  }
  return (mask: number) => {
    let r = 0;
    let j = 1;
    while (mask) {
      const b = ctz(mask);
      mask &= mask - 1;
      r += C[b]![j++]!;
    }
    return r + 1;
  };
}

/** The canonical local order for common pair C = {ca, cb}: intact pairs, then the partners of C's points. */
export function contextOrder(h: number, ca: number, cb: number): number[] {
  const common = (1 << ca) | (1 << cb);
  const order: number[] = [];
  for (let x = 0; x < h; x += 2) if (!(common & (3 << x))) order.push(x, x + 1);
  for (let x = 0; x < h; x++) if (!(common & (1 << x)) && common & (1 << (x ^ 1))) order.push(x);
  return order;
}

/** Local records: core (local mask) and, for core size 1, the remaining pairs; for size 2, the remaining points. */
function localRecords(g: ActiveGraph) {
  const rep = verifyPairedTriple(g);
  if (!rep.outputsExact || !rep.totalExact || !rep.allDisjoint) throw new Error("local producer not exact");
  const { V, n } = g;
  const words = (V + 31) >>> 5;
  const triples: number[] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) triples.push((1 << a) | (1 << b) | (1 << c));
  const A = g.left.length;
  const sup = new Uint32Array((V + 1 + A) * words);
  for (let i = 0; i < V; i++) sup[(i + 1) * words + (i >>> 5)]! |= 1 << (i & 31);
  const offs = new Int32Array(A + 1);
  const vars: number[] = [];
  for (let k = 0; k < A; k++) {
    const x = V + 1 + k;
    const a = g.left[k]!;
    const b = g.right[k]!;
    for (let w = 0; w < words; w++) sup[x * words + w] = sup[a * words + w]! | sup[b * words + w]!;
    const core = rep.core[x]!;
    const nc = pop32(core);
    if (nc >= 1)
      for (let i = 0; i < V; i++)
        if ((sup[x * words + (i >>> 5)]! >>> (i & 31)) & 1) {
          const rest = triples[i]! & ~core;
          if (nc === 1) vars.push(rest); // two remaining local points, as a mask
          else vars.push(rest); // one remaining local point, as a mask
        }
    offs[k + 1] = vars.length;
  }
  return { core: rep.core, offs, vars: Int32Array.from(vars), report: rep };
}

/** Open-addressing table of exact keys of fixed word length; values are global node ids. */
class KeyTable {
  private slots: Int32Array;
  private mask: number;
  private pool: Uint32Array;
  private vals: Int32Array;
  count = 0;
  constructor(readonly width: number, logCap: number, initialEntries: number) {
    this.slots = new Int32Array(1 << logCap).fill(-1);
    this.mask = (1 << logCap) - 1;
    this.pool = new Uint32Array(initialEntries * width);
    this.vals = new Int32Array(initialEntries);
  }
  private hash(k: Uint32Array): number {
    let h = 0x811c9dc5 | 0;
    for (let i = 0; i < this.width; i++) {
      h = Math.imul(h ^ k[i]!, 0x01000193);
      h ^= h >>> 15;
      h = Math.imul(h, 0x2c1b3c6d);
    }
    h ^= h >>> 13;
    return h >>> 0;
  }
  /** Returns the existing value, or inserts `val` and returns -1. */
  getOrInsert(k: Uint32Array, val: number): number {
    if (this.count * 10 > this.slots.length * 7) this.rehash();
    let s = this.hash(k) & this.mask;
    const W = this.width;
    for (;;) {
      const e = this.slots[s]!;
      if (e < 0) break;
      let same = true;
      for (let i = 0; i < W; i++)
        if (this.pool[e * W + i] !== k[i]) {
          same = false;
          break;
        }
      if (same) return this.vals[e]!;
      s = (s + 1) & this.mask;
    }
    if (this.count === this.vals.length) {
      const grown = Math.ceil(this.vals.length * 1.5);
      const pool = new Uint32Array(grown * this.width);
      pool.set(this.pool);
      this.pool = pool;
      const vals = new Int32Array(grown);
      vals.set(this.vals);
      this.vals = vals;
    }
    const e = this.count++;
    this.pool.set(k, e * W);
    this.vals[e] = val;
    this.slots[s] = e;
    return -1;
  }
  private rehash() {
    const old = this.slots;
    this.slots = new Int32Array(old.length * 2).fill(-1);
    this.mask = this.slots.length - 1;
    const W = this.width;
    const k = new Uint32Array(W);
    for (let e = 0; e < this.count; e++) {
      for (let i = 0; i < W; i++) k[i] = this.pool[e * W + i]!;
      let s = this.hash(k) & this.mask;
      while (this.slots[s]! >= 0) s = (s + 1) & this.mask;
      this.slots[s] = e;
    }
  }
}

class Growable {
  a: Int32Array;
  n = 0;
  constructor(cap: number) {
    this.a = new Int32Array(cap);
  }
  push(x: number) {
    if (this.n === this.a.length) {
      const b = new Int32Array(this.a.length * 2);
      b.set(this.a);
      this.a = b;
    }
    this.a[this.n++] = x;
  }
}

export type GlobalProducer = {
  h: number;
  v: number; // inputs: global ids 1..v
  left: Int32Array; // per global node id (inputs 0 / 0)
  right: Int32Array;
  core: Int32Array; // common points of the support, as a mask over [h]
  starMask: Int32Array; // for core size 4: the remaining points
  roots: Int32Array; // designated outputs (with repetition)
  uniqueAdditions: number;
  byCoreSize: Record<number, number>; // unique additions by |core| (2, 3, 4)
  merged: number; // local additions identified with an existing global node
  contexts: number;
};

/** Global identification of the C(h,2) local producers (exact keys). */
export function mergeProducers(h: number, g: ActiveGraph): GlobalProducer {
  if (h % 2 || h > 30 || g.n !== h - 2) throw new Error("need even h <= 30 and a local producer on h - 2 points");
  const loc = localRecords(g);
  const { V } = g;
  const A = g.left.length;
  const rank5 = makeRank(h);
  // the inputs
  const fives: number[] = [];
  for (let m = 0; m < 1 << h; m++) if (pop32(m) === 5) fives.push(m);
  const v = fives.length;
  // capacity: the number of nodes without any identification (an upper bound; no regrowth)
  const cap = v + 1 + ((h * (h - 1)) / 2) * A;
  const left = new Growable(cap);
  const right = new Growable(cap);
  const core = new Growable(cap);
  const star = new Growable(cap);
  left.push(0);
  right.push(0);
  core.push(0);
  star.push(0);
  for (let i = 0; i < v; i++) {
    left.push(0);
    right.push(0);
    core.push(0);
    star.push(0);
  }
  for (const m of fives) core.a[rank5(m)] = m;
  const P = (h * (h - 1)) / 2;
  const pairIdx = (a: number, b: number) => {
    if (a > b) [a, b] = [b, a];
    return a * h - (a * (a + 1)) / 2 + (b - a - 1);
  };
  const W3 = 1 + ((P + 31) >>> 5);
  const t3 = new KeyTable(W3, 22, 1 << 20);
  const t4 = new KeyTable(2, 22, 1 << 20);
  const key3 = new Uint32Array(W3);
  const key4 = new Uint32Array(2);
  const roots = new Growable(1 << 16);
  const ids = new Int32Array(V + 1 + A);
  const byCoreSize: Record<number, number> = { 2: 0, 3: 0, 4: 0 };
  let merged = 0;
  let contexts = 0;
  const localTriples: number[] = [];
  const n = h - 2;
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) localTriples.push((1 << a) | (1 << b) | (1 << c));
  const newNode = (a: number, b: number, c: number, s: number) => {
    const id = left.n;
    left.push(a);
    right.push(b);
    core.push(c);
    star.push(s);
    return id;
  };
  for (let ca = 0; ca < h; ca++)
    for (let cb = ca + 1; cb < h; cb++) {
      contexts++;
      const order = contextOrder(h, ca, cb);
      const common = (1 << ca) | (1 << cb);
      const toGlobal = (m: number) => {
        let r = 0;
        while (m) {
          r |= 1 << order[ctz(m)]!;
          m &= m - 1;
        }
        return r;
      };
      for (let i = 1; i <= V; i++) ids[i] = rank5(common | toGlobal(localTriples[i - 1]!));
      for (let k = 0; k < A; k++) {
        const x = V + 1 + k;
        const a = ids[g.left[k]!]!;
        const b = ids[g.right[k]!]!;
        const gc = common | toGlobal(loc.core[x]!);
        const nc = pop32(gc);
        let id: number;
        if (nc === 2) {
          id = newNode(a, b, gc, 0);
          byCoreSize[2]!++;
        } else if (nc === 3) {
          key3.fill(0);
          key3[0] = gc;
          for (let j = loc.offs[k]!; j < loc.offs[k + 1]!; j++) {
            const r = toGlobal(loc.vars[j]!);
            const u = ctz(r);
            const w = ctz(r & (r - 1));
            const pi = pairIdx(u, w);
            key3[1 + (pi >>> 5)]! |= 1 << (pi & 31);
          }
          const found = t3.getOrInsert(key3, left.n);
          if (found >= 0) {
            id = found;
            merged++;
          } else {
            id = newNode(a, b, gc, 0);
            byCoreSize[3]!++;
          }
        } else if (nc === 4) {
          let sm = 0;
          for (let j = loc.offs[k]!; j < loc.offs[k + 1]!; j++) sm |= toGlobal(loc.vars[j]!);
          key4[0] = gc;
          key4[1] = sm;
          const found = t4.getOrInsert(key4, left.n);
          if (found >= 0) {
            id = found;
            merged++;
          } else {
            id = newNode(a, b, gc, sm);
            byCoreSize[4]!++;
          }
        } else throw new Error(`addition with ${nc} common points`);
        ids[x] = id;
      }
      for (const o of g.outputs) roots.push(ids[o]!);
      roots.push(ids[g.total]!);
    }
  return {
    h,
    v,
    left: left.a.subarray(0, left.n),
    right: right.a.subarray(0, right.n),
    core: core.a.subarray(0, core.n),
    starMask: star.a.subarray(0, star.n),
    roots: roots.a.subarray(0, roots.n),
    uniqueAdditions: left.n - v - 1,
    byCoreSize,
    merged,
    contexts,
  };
}

/** Remove additions not reachable from a root. Returns the active flags and counts. */
export function prune(G: GlobalProducer) {
  const N = G.left.length;
  const active = new Uint8Array(N);
  const stack = new Growable(1 << 20);
  for (const r of G.roots) stack.push(r);
  let additions = 0;
  let inputs = 0;
  let topological = true;
  while (stack.n) {
    const x = stack.a[--stack.n]!;
    if (active[x]) continue;
    active[x] = 1;
    if (x > G.v) {
      additions++;
      const a = G.left[x]!;
      const b = G.right[x]!;
      if (!(a > 0 && a < x && b > 0 && b < x)) topological = false;
      stack.push(a);
      stack.push(b);
    } else inputs++;
  }
  return { active, additions, inputs, topological, removed: G.uniqueAdditions - additions };
}

/** Requested sums of every star: the star's nodes used outside it or designated as outputs. */
export function starDemands(G: GlobalProducer, active: Uint8Array) {
  const N = G.left.length;
  const needed = new Uint8Array(N);
  const sizes = new Map<number, number>();
  for (let x = G.v + 1; x < N; x++) {
    if (!active[x]) continue;
    const cx = G.core[x]!;
    if (pop32(cx) === 4) sizes.set(cx, (sizes.get(cx) ?? 0) + 1);
    for (const a of [G.left[x]!, G.right[x]!]) if (pop32(G.core[a]!) === 4 && G.core[a] !== cx) needed[a] = 1;
  }
  for (const r of G.roots) if (pop32(G.core[r]!) === 4) needed[r] = 1;
  const demand = new Map<number, number[]>();
  for (let x = G.v + 1; x < N; x++)
    if (needed[x]) {
      const c = G.core[x]!;
      if (!demand.has(c)) demand.set(c, []);
      demand.get(c)!.push(G.starMask[x]!);
    }
  // stars with additions but no request cannot occur when nothing is pruned; record them anyway
  let oldStarAdditions = 0;
  for (const s of sizes.values()) oldStarAdditions += s;
  return { demand, sizes, oldStarAdditions, stars: sizes.size };
}

/** Canonical relabelling of a star's request list: intact pairs first, then partners of B's points. */
export function canonicalRequests(h: number, B: number, masks: number[]): number[] {
  const order: number[] = [];
  for (let x = 0; x < h; x++) if (!(B & (1 << x)) && !(B & (1 << (x ^ 1)))) order.push(x);
  for (let x = 0; x < h; x++) if (!(B & (1 << x)) && B & (1 << (x ^ 1))) order.push(x);
  if (order.length !== h - 4) throw new Error("bad star order");
  const out = masks.map((m) => {
    let z = 0;
    order.forEach((x, j) => {
      if (m & (1 << x)) z |= 1 << j;
    });
    return z >>> 0;
  });
  return [...new Set(out)].sort((a, b) => a - b);
}

/**
 * The note's greedy rule: repeatedly add the pair of current terms that occurs in the most
 * requested sums (each request is kept as a partition of its support into current terms); ties
 * by increasing union size, then union mask, then operand masks; an already built union is
 * reused (and also absorbs any request whose current terms partition it). Returns the gates.
 */
export function greedyCSE(masks: number[]): [number, number][] {
  const leavesSet = new Set<number>();
  for (const m of masks) for (let i = 0; i < 31; i++) if ((m >>> i) & 1) leavesSet.add(1 << i);
  const terms: Set<number>[] = masks.map((m) => new Set([...leavesSet].filter((x) => (m & x) !== 0)));
  const nodes = new Set<number>(leavesSet);
  const gates: [number, number][] = [];
  while (terms.some((t) => t.size > 1)) {
    const freq = new Map<number, number>(); // key: a * 2^24 + b would overflow; use string-free double key
    const keyOf = (a: number, b: number) => a * 33554432 + b; // a, b < 2^25 here
    for (const t of terms) {
      const s = [...t].sort((x, y) => x - y);
      for (let i = 0; i < s.length; i++) for (let j = i + 1; j < s.length; j++) {
        const k = keyOf(s[i]!, s[j]!);
        freq.set(k, (freq.get(k) ?? 0) + 1);
      }
    }
    let best = -1;
    let bf = -1;
    let bu = 0;
    let bc = 0;
    for (const [k, f] of freq) {
      const a = Math.floor(k / 33554432);
      const b = k - a * 33554432;
      const u = (a | b) >>> 0;
      const c = pop32(u);
      // better: higher f; then smaller c; then smaller u; then smaller (a, b)
      if (best < 0 || f > bf || (f === bf && (c < bc || (c === bc && (u < bu || (u === bu && k < best)))))) {
        best = k;
        bf = f;
        bu = u;
        bc = c;
      }
    }
    const a = Math.floor(best / 33554432);
    const b = best - a * 33554432;
    if ((a & b) !== 0) throw new Error("greedy joined overlapping terms");
    const node = (a | b) >>> 0;
    if (!nodes.has(node)) {
      nodes.add(node);
      gates.push([a, b]);
    }
    for (const t of terms)
      if (t.has(a) && t.has(b)) {
        t.delete(a);
        t.delete(b);
        t.add(node);
      }
    for (const t of terms) {
      const contained = [...t].filter((x) => (x & ~node) === 0);
      if (contained.length > 1 && contained.reduce((s, x) => s + x, 0) === node) {
        for (const x of contained) t.delete(x);
        t.add(node);
      }
    }
  }
  terms.forEach((t, i) => {
    if (t.size !== 1 || [...t][0] !== masks[i]) throw new Error("greedy did not produce a requested sum");
  });
  return gates;
}

/** Independent check of a template: every gate joins two disjoint available masks, makes a new one, and every request is made. */
export function checkTemplate(width: number, targets: number[], gates: [number, number][]): boolean {
  const have = new Set<number>();
  for (let i = 0; i < width; i++) have.add(2 ** i);
  for (const [a, b] of gates) {
    if (!(have.has(a) && have.has(b))) return false;
    if ((a & b) !== 0) return false;
    const u = (a | b) >>> 0;
    if (have.has(u)) return false;
    have.add(u);
  }
  return targets.every((t) => have.has(t));
}

export function resynthesize(G: GlobalProducer, d: ReturnType<typeof starDemands>) {
  const cache = new Map<string, { targets: number[]; gates: [number, number][]; ok: boolean; uses: number }>();
  let newStarAdditions = 0;
  let allTemplatesValid = true;
  let unrequestedStars = 0;
  for (const [B] of d.sizes) {
    const masks = d.demand.get(B);
    if (!masks) {
      unrequestedStars++;
      continue;
    }
    const targets = canonicalRequests(G.h, B, masks);
    const k = targets.join(",");
    let t = cache.get(k);
    if (!t) {
      const gates = greedyCSE(targets);
      t = { targets, gates, ok: checkTemplate(G.h - 4, targets, gates), uses: 0 };
      cache.set(k, t);
      if (!t.ok) allTemplatesValid = false;
    }
    newStarAdditions += t.gates.length;
    t.uses++; // number of stars using this template (PR 9 re-synthesizes per template)
  }
  return { templates: cache.size, newStarAdditions, allTemplatesValid, unrequestedStars, cache };
}

/**
 * Second route to the number of distinct supports: 128-bit additive fingerprints
 * (four independent 32-bit lanes of a fixed pseudo-random value per five-set, summed modulo 2^32).
 * For disjoint additions the fingerprint of a sum is the sum of the fingerprints, so every local
 * node's fingerprint follows from its children. Two different supports collide with probability
 * 2^-128 per pair. Returns the number of distinct fingerprints of local additions over all contexts.
 */
export function fingerprintCount(h: number, g: ActiveGraph, seed = 0x9e3779b9) {
  const { V } = g;
  const A = g.left.length;
  const n = h - 2;
  const rank5 = makeRank(h);
  let v = 0;
  for (let m = 0; m < 1 << h; m++) if (pop32(m) === 5) v++;
  // xorshift-based pseudo-random lanes
  let s = seed >>> 0;
  const rnd = () => {
    s ^= s << 13;
    s >>>= 0;
    s ^= s >>> 17;
    s ^= s << 5;
    s >>>= 0;
    return s;
  };
  const lanes = new Uint32Array((v + 1) * 4);
  for (let i = 4; i < lanes.length; i++) lanes[i] = rnd();
  const localTriples: number[] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) localTriples.push((1 << a) | (1 << b) | (1 << c));
  const table = new KeyTable(4, 22, 1 << 20);
  const fp = new Uint32Array((V + 1 + A) * 4);
  const key = new Uint32Array(4);
  let distinct = 0;
  for (let ca = 0; ca < h; ca++)
    for (let cb = ca + 1; cb < h; cb++) {
      const order = contextOrder(h, ca, cb);
      const common = (1 << ca) | (1 << cb);
      for (let i = 1; i <= V; i++) {
        let m = localTriples[i - 1]!;
        let r = common;
        while (m) {
          r |= 1 << order[ctz(m)]!;
          m &= m - 1;
        }
        const id = rank5(r);
        for (let l = 0; l < 4; l++) fp[i * 4 + l] = lanes[id * 4 + l]!;
      }
      for (let k = 0; k < A; k++) {
        const x = V + 1 + k;
        const a = g.left[k]!;
        const b = g.right[k]!;
        for (let l = 0; l < 4; l++) {
          const z = (fp[a * 4 + l]! + fp[b * 4 + l]!) >>> 0;
          fp[x * 4 + l] = z;
          key[l] = z;
        }
        if (table.getOrInsert(key, 1) < 0) distinct++;
      }
    }
  return { distinct, v };
}
