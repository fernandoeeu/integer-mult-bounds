// The paired-block exclusion circuit, rebuilt from its description in
// notes/paired-construction.tex, subsection "A paired-block circuit for the
// bit correction" (sec:paired-bit-construction).
//
// Problem. Fix a common point i; on the other n = h-1 points, inputs x_ab
// (a < b) stand for the source triples {i,a,b}. Required outputs:
//     z_cd = sum of x_ab over pairs {a,b} disjoint from {c,d}.
//
// Every node of the circuit is a formal sum of inputs, identified by its
// support (the set of input pairs it adds). Additions only ever combine nodes
// with disjoint supports ("the computation below always adds disjoint formal
// input supports"), and equal supports are interned: the first node created
// with a given support is kept together with its decomposition.
//
// Weighted recursion (the note's notation):
//   a graph has vertex values w_u and edge values e_uv (disjoint supports);
//   group the ordered vertices into consecutive pairs (last one may be single);
//   coarse weight  w~_A  = sum_{u in A} w_u + sum_{u<v in A} e_uv,
//   coarse edge    e~_AB = sum_{u in A, v in B} e_uv;
//   recursively get O_A (coarse value with block A deleted) and F_AB (A,B deleted);
//   for a in A with partner a' (A \ {a} = {a'} or empty):
//     C_a      = w_{a'},
//     E_{a,C}  = sum_{v in C} e_{a'v},
//     H_{a;B}  = C_a + sum_{C != A,B} E_{a,C}   (leave-one-out prefix/suffix),
//     H_a      = C_a + sum_{C != A} E_{a,C};
//   outputs: a,b in different blocks A,B:
//     F_ab = (F_AB + H_{a;B}) + (H_{b;A} + e_{a'b'}),
//   a,b in one block A: F_ab = O_A;   single deletion: O_a = O_A + H_a.
//   Graphs with at most four vertices are summed directly.
//
// The note fixes the algebra but not every summation order, and the number of
// additions depends on the order through interning. The three choices that
// change the count are collected in `Conventions` (see README, "Conventions").

export type Conventions = {
  /** Balanced binary addition splits a list of k terms at floor(k/2) or ceil(k/2). */
  split: "floor" | "ceil";
  /** Zero terms (empty supports) stay in the list when it is split (true) or are dropped first (false). */
  zerosTakePart: boolean;
  /** In the direct sums for at most four vertices, list vertex weights before edges (true) or after (false). */
  baseWeightsFirst: boolean;
};

/** Reproduces the published circuit: 9813 local additions, c = 450394 at h = 50. */
export const PUBLISHED_CONVENTIONS: Conventions = { split: "floor", zerosTakePart: true, baseWeightsFirst: false };

/** A different reading of the same description: 9810 local additions, c = 450244 at h = 50. */
export const ALTERNATIVE_CONVENTIONS: Conventions = { split: "ceil", zerosTakePart: false, baseWeightsFirst: true };

const NONE = -1; // the zero node (empty support)

/** Index of the unordered pair {a,b}, a != b, among n points (lexicographic). */
export function pairIndex(n: number, a: number, b: number): number {
  if (a > b) [a, b] = [b, a];
  return a * n - (a * (a + 1)) / 2 + (b - a - 1);
}

export type Circuit = {
  n: number;
  inputs: number; // node ids 0 .. inputs-1 are the inputs x_ab
  left: number[]; // for addition node id = inputs + k: children left[k], right[k]
  right: number[];
  outputs: Int32Array; // outputs[pairIndex(c,d)] = node computing z_cd
};

function keyOf(s: Uint32Array): string {
  let k = "";
  for (let i = 0; i < s.length; i++) k += String.fromCharCode(s[i]! & 0xffff, s[i]! >>> 16);
  return k;
}

export function buildPairedCircuit(n: number, conv: Conventions = PUBLISHED_CONVENTIONS): Circuit {
  const P = (n * (n - 1)) / 2;
  const W = (P + 31) >>> 5;
  const supports: Uint32Array[] = [];
  const left: number[] = [];
  const right: number[] = [];
  const byKey = new Map<string, number>();

  for (let k = 0; k < P; k++) {
    const s = new Uint32Array(W);
    s[k >>> 5]! |= 1 << (k & 31);
    supports.push(s);
    byKey.set(keyOf(s), k);
  }

  // x + y with interning; NONE is the zero sum.
  function add(x: number, y: number): number {
    if (x === NONE) return y;
    if (y === NONE) return x;
    const sx = supports[x]!;
    const sy = supports[y]!;
    const u = new Uint32Array(W);
    for (let i = 0; i < W; i++) {
      if ((sx[i]! & sy[i]!) !== 0) throw new Error("addition of overlapping supports");
      u[i] = sx[i]! | sy[i]!;
    }
    const key = keyOf(u);
    const found = byKey.get(key);
    if (found !== undefined) return found; // keep the first decomposition
    const id = supports.length;
    supports.push(u);
    left.push(x);
    right.push(y);
    byKey.set(key, id);
    return id;
  }

  // "balanced binary addition"
  function sumTerms(terms: number[]): number {
    const t = conv.zerosTakePart ? terms : terms.filter((x) => x !== NONE);
    if (t.length === 0) return NONE;
    if (t.length === 1) return t[0]!;
    const mid = conv.split === "floor" ? t.length >> 1 : (t.length + 1) >> 1;
    return add(sumTerms(t.slice(0, mid)), sumTerms(t.slice(mid)));
  }

  type Level = { O: number[]; F: number[][] };

  // k vertices, weights w[u], symmetric edge table e[u][v]. Returns the values
  // after deleting one vertex (O) and two vertices (F).
  function solve(k: number, w: number[], e: number[][]): Level {
    const F: number[][] = Array.from({ length: k }, () => new Array<number>(k).fill(NONE));
    const all = [...Array(k).keys()];

    if (k <= 4) {
      // direct sums of the surviving weighted graph
      const survivors = (deleted: number[]) => {
        const alive = all.filter((u) => !deleted.includes(u));
        const ws = alive.map((u) => w[u]!);
        const es: number[] = [];
        for (const u of alive) for (const v of alive) if (u < v) es.push(e[u]![v]!);
        return sumTerms(conv.baseWeightsFirst ? [...ws, ...es] : [...es, ...ws]);
      };
      const O = all.map((u) => survivors([u]));
      for (let u = 0; u < k; u++) for (let v = u + 1; v < k; v++) F[u]![v] = F[v]![u] = survivors([u, v]);
      return { O, F };
    }

    // consecutive blocks {0,1},{2,3},..., possibly a final singleton
    const blocks: number[][] = [];
    for (let u = 0; u < k; u += 2) blocks.push(u + 1 < k ? [u, u + 1] : [u]);
    const K = blocks.length;
    const blockOf = (u: number) => u >> 1;
    const partner = (u: number) => {
      const A = blocks[blockOf(u)]!;
      return A.length === 2 ? (A[0] === u ? A[1]! : A[0]!) : NONE;
    };

    // w~_A = sum_{u in A} w_u + sum_{u<v in A} e_uv
    const wCoarse = blocks.map((A) => {
      const internal = A.length === 2 ? [e[A[0]!]![A[1]!]!] : [];
      return sumTerms([...A.map((u) => w[u]!), ...internal]);
    });
    // e~_AB = sum_{u in A, v in B} e_uv
    const eCoarse: number[][] = Array.from({ length: K }, () => new Array<number>(K).fill(NONE));
    for (let A = 0; A < K; A++)
      for (let B = A + 1; B < K; B++) {
        const terms: number[] = [];
        for (const u of blocks[A]!) for (const v of blocks[B]!) terms.push(e[u]![v]!);
        eCoarse[A]![B] = eCoarse[B]![A] = sumTerms(terms);
      }

    const coarse = solve(K, wCoarse, eCoarse);

    // H_{a;B} for every vertex a and every other block B, and H_a,
    // by the leave-one-out prefix/suffix routine on (C_a, (E_{a,C})_{C != A}).
    const Hleave: number[][] = Array.from({ length: k }, () => new Array<number>(K).fill(NONE));
    const Htotal = new Array<number>(k).fill(NONE);
    for (let a = 0; a < k; a++) {
      const A = blockOf(a);
      const ap = partner(a);
      const others = [...Array(K).keys()].filter((C) => C !== A);
      const vec = [
        ap === NONE ? NONE : w[ap]!, // C_a
        ...others.map((C) => (ap === NONE ? NONE : sumTerms(blocks[C]!.map((v) => e[ap]![v]!)))), // E_{a,C}
      ];
      const r = vec.length - 1;
      const prefix = new Array<number>(r + 1);
      prefix[0] = vec[0]!;
      for (let i = 1; i <= r; i++) prefix[i] = add(prefix[i - 1]!, vec[i]!);
      const suffix = new Array<number>(r + 2).fill(NONE);
      for (let i = r; i >= 2; i--) suffix[i] = add(vec[i]!, suffix[i + 1]!); // only suffixes that are requested
      for (let i = 1; i <= r; i++) Hleave[a]![others[i - 1]!] = add(prefix[i - 1]!, suffix[i + 1]!);
      Htotal[a] = prefix[r]!;
    }

    // a, b in one block A: F_ab = O_A
    for (const [u, v] of blocks) if (v !== undefined) F[u!]![v] = F[v]![u!] = coarse.O[blockOf(u!)]!;
    // a in A, b in B, A != B: F_ab = (F_AB + H_{a;B}) + (H_{b;A} + e_{a'b'})
    for (let a = 0; a < k; a++)
      for (let b = a + 1; b < k; b++) {
        const A = blockOf(a);
        const B = blockOf(b);
        if (A === B) continue;
        const ap = partner(a);
        const bp = partner(b);
        const cross = ap === NONE || bp === NONE ? NONE : e[ap]![bp]!;
        const first = add(coarse.F[A]![B]!, Hleave[a]![B]!);
        const second = add(Hleave[b]![A]!, cross);
        F[a]![b] = F[b]![a] = add(first, second);
      }
    // single deletion: O_a = O_A + H_a (unused at the root; pruned there)
    const O = all.map((a) => add(coarse.O[blockOf(a)]!, Htotal[a]!));
    return { O, F };
  }

  // root: w_u = 0 and e_uv = x_uv
  const e0: number[][] = Array.from({ length: n }, (_, a) =>
    Array.from({ length: n }, (_, b) => (a === b ? NONE : pairIndex(n, a, b))),
  );
  const root = solve(n, new Array<number>(n).fill(NONE), e0);

  const outputs = new Int32Array(P);
  for (let c = 0; c < n; c++) for (let d = c + 1; d < n; d++) outputs[pairIndex(n, c, d)] = root.F[c]![d]!;

  return pruneUnused({ n, inputs: P, left, right, outputs });
}

/**
 * "Remove unused nodes": keep only additions reachable from a designated
 * output, renumbered in creation order (which is a topological order).
 */
export function pruneUnused(c: Circuit): Circuit {
  const total = c.inputs + c.left.length;
  const used = new Uint8Array(total);
  const stack = Array.from(c.outputs);
  while (stack.length) {
    const x = stack.pop()!;
    if (x < 0 || used[x]) continue;
    used[x] = 1;
    if (x >= c.inputs) stack.push(c.left[x - c.inputs]!, c.right[x - c.inputs]!);
  }
  const renum = new Int32Array(total).fill(-1);
  for (let i = 0; i < c.inputs; i++) renum[i] = i;
  const left: number[] = [];
  const right: number[] = [];
  for (let k = 0; k < c.left.length; k++) {
    const id = c.inputs + k;
    if (!used[id]) continue;
    renum[id] = c.inputs + left.length;
    left.push(renum[c.left[k]!]!);
    right.push(renum[c.right[k]!]!);
  }
  return { n: c.n, inputs: c.inputs, left, right, outputs: c.outputs.map((x) => renum[x]!) };
}
