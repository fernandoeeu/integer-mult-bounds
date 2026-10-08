// PR 8 (Rohan Arun): the two side circuits of the "geometric envelope" complex
// network, rebuilt from research/geometric-complex/geometric-note.tex, section
// "Two exact scalar circuits", which fixes the construction completely:
//
//   "Order all triples lexicographically and assign them indices 0..v-1. A singleton
//    support is its input variable. For any larger requested support, take the smallest
//    dyadic interval of indices containing it and split at that interval's midpoint.
//    Recursively construct the two nonempty parts and add them. Intern equal supports,
//    and discard nodes not reaching any requested output."
//
// Requested supports:
//   D: for every target triple S, the triples disjoint from S (2300 outputs at n = 25);
//   E: for every pair P and every target S containing P, the triples containing P other
//      than S (C(25,2) * 23 = 6900 partial outputs).
// The circuit is a function of the requested family only (no order enters), so the
// counts here are an independent reconstruction from the prose. The Python was not read.

const popcount = (x: number) => {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
};

export function triplesLex(n: number): number[] {
  const out: number[] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) out.push((1 << a) | (1 << b) | (1 << c));
  return out;
}

export type DyadicCircuit = {
  v: number;
  additions: number; // distinct non-singleton supports reachable from the outputs
  outputs: number; // requested outputs (with repetition)
  outputsExact: boolean; // every output node's support equals its requested set
  allDisjoint: boolean; // every addition joins disjoint supports whose union is the node
  maxDepth: number;
  nodes: Map<string, { lo: number; hi: number; size: number }>; // key -> children keys are implicit
};

/** Build the dyadic-split DAG for a family of requested index sets (sorted, distinct indices). */
export function dyadicCircuit(v: number, requests: number[][]): DyadicCircuit {
  const words = (v + 31) >>> 5;
  const nodes = new Map<string, { lo: number; hi: number; size: number }>();
  const keyOf = (idx: number[]) => {
    const b = new Uint32Array(words);
    for (const i of idx) b[i >>> 5]! |= 1 << (i & 31);
    let k = "";
    for (let i = 0; i < words; i++) k += String.fromCharCode(b[i]! & 0xffff, b[i]! >>> 16);
    return { k, b };
  };
  let allDisjoint = true;
  let maxDepth = 0;
  const build = (idx: number[], depth: number): Uint32Array => {
    const { k, b } = keyOf(idx);
    if (idx.length === 1) return b;
    if (nodes.has(k)) return b;
    maxDepth = Math.max(maxDepth, depth);
    const lo = idx[0]!;
    const hi = idx[idx.length - 1]!;
    // smallest dyadic interval [base, base + 2^j) containing lo..hi: j = bit length of lo XOR hi
    const j = 32 - Math.clz32(lo ^ hi);
    const mid = ((lo >>> j) << j) + (1 << (j - 1));
    const L = idx.filter((x) => x < mid);
    const R = idx.filter((x) => x >= mid);
    if (L.length === 0 || R.length === 0) throw new Error("a dyadic part is empty");
    const bl = build(L, depth + 1);
    const br = build(R, depth + 1);
    for (let w = 0; w < words; w++) {
      if ((bl[w]! & br[w]!) !== 0) allDisjoint = false;
      if (((bl[w]! | br[w]!) >>> 0) !== b[w]) allDisjoint = false;
    }
    nodes.set(k, { lo, hi, size: idx.length });
    return b;
  };
  let outputsExact = true;
  for (const r of requests) {
    const b = build(r, 0);
    // the node returned for r must have exactly r as support
    let cnt = 0;
    for (let w = 0; w < words; w++) cnt += popcount(b[w]!);
    if (cnt !== r.length || !r.every((i) => ((b[i >>> 5]! >>> (i & 31)) & 1) === 1)) outputsExact = false;
  }
  return { v, additions: nodes.size, outputs: requests.length, outputsExact, allDisjoint, maxDepth, nodes };
}

/** D requests: for every triple S, the triples disjoint from S. */
export function disjointRequests(n: number): number[][] {
  const T = triplesLex(n);
  return T.map((S) => T.map((t, i) => ((t & S) === 0 ? i : -1)).filter((i) => i >= 0));
}

/** E requests: for every pair P (lexicographic) and every target S containing P (by index), the triples containing P except S. */
export function intersectionTwoRequests(n: number): { requests: number[][]; targets: number[]; pairs: number[] } {
  const T = triplesLex(n);
  const requests: number[][] = [];
  const targets: number[] = [];
  const pairs: number[] = [];
  for (let a = 0; a < n; a++)
    for (let b = a + 1; b < n; b++) {
      const P = (1 << a) | (1 << b);
      const star = T.map((t, i) => ((t & P) === P ? i : -1)).filter((i) => i >= 0);
      for (const s of star) {
        requests.push(star.filter((i) => i !== s));
        targets.push(s);
        pairs.push(P);
      }
    }
  return { requests, targets, pairs };
}

/**
 * The side map assembled from the two circuits: (1/2) D - (1/2) E, compared coefficient by
 * coefficient with the required map (+1/2 on disjoint, -1/2 on intersection two, 0 otherwise),
 * each triple covered at most once per target.
 */
export function sideMapExact(n: number): { exact: boolean; nonzero: number } {
  const E = intersectionTwoRequests(n);
  return sideMapExactFor(n, disjointRequests(n), E.requests, E.targets);
}

/** The same comparison for given request lists (D indexed by target; E with its targets). */
export function sideMapExactFor(n: number, D: number[][], E: number[][], Etargets: number[]): { exact: boolean; nonzero: number } {
  const T = triplesLex(n);
  const v = T.length;
  const coef = Array.from({ length: v }, () => new Int8Array(v));
  let exact = true;
  D.forEach((r, s) => {
    for (const i of r) {
      if (coef[s]![i] !== 0) exact = false;
      coef[s]![i] = 1;
    }
  });
  E.forEach((r, k) => {
    const s = Etargets[k]!;
    for (const i of r) {
      if (coef[s]![i] !== 0) exact = false;
      coef[s]![i] = -1;
    }
  });
  let nonzero = 0;
  for (let s = 0; s < v; s++)
    for (let i = 0; i < v; i++) {
      const k = popcount(T[s]! & T[i]!);
      const want = k === 0 ? 1 : k === 2 ? -1 : 0;
      if (coef[s]![i] !== want) exact = false;
      if (want) nonzero++;
    }
  return { exact, nonzero };
}
