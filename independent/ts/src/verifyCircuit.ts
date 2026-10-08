// Independent verification of a local exclusion circuit.
//
// This does not trust anything the builder computed except the list of
// additions (left/right children) and the designated outputs. It recomputes
// every node's support from scratch, checks that every addition joins
// disjoint supports, and compares each output support with its definition
//     supp(z_cd) = { {a,b} : {a,b} disjoint from {c,d} }
// in both directions (every required coefficient present, every required zero
// absent). Source: paired-construction.tex, "All 1271256 nonzero
// coefficients, and every required zero, are checked by comparing all output
// supports with their definitions."

import { type Circuit, pairIndex } from "./circuit";

export type LocalReport = {
  n: number;
  additions: number;
  outputs: number;
  nonzeroCoefficients: number;
  allAdditionsDisjoint: boolean;
  allOutputSupportsExact: boolean;
  everyAdditionUsed: boolean;
};

export function supportsOf(c: Circuit): Uint32Array[] {
  const P = c.inputs;
  const W = (P + 31) >>> 5;
  const s: Uint32Array[] = [];
  for (let k = 0; k < P; k++) {
    const b = new Uint32Array(W);
    b[k >>> 5]! |= 1 << (k & 31);
    s.push(b);
  }
  for (let k = 0; k < c.left.length; k++) {
    const l = c.left[k]!;
    const r = c.right[k]!;
    if (!(l < P + k && r < P + k)) throw new Error("addition uses a later node");
    const u = new Uint32Array(W);
    for (let i = 0; i < W; i++) u[i] = s[l]![i]! | s[r]![i]!;
    s.push(u);
  }
  return s;
}

function disjoint(x: Uint32Array, y: Uint32Array) {
  for (let i = 0; i < x.length; i++) if ((x[i]! & y[i]!) !== 0) return false;
  return true;
}

const has = (s: Uint32Array, k: number) => ((s[k >>> 5]! >>> (k & 31)) & 1) === 1;

export function verifyLocalCircuit(c: Circuit): LocalReport {
  const { n, inputs: P } = c;
  const s = supportsOf(c);

  let allAdditionsDisjoint = true;
  for (let k = 0; k < c.left.length; k++) if (!disjoint(s[c.left[k]!]!, s[c.right[k]!]!)) allAdditionsDisjoint = false;

  let exact = c.outputs.length === P;
  let nonzero = 0;
  for (let cc = 0; cc < n; cc++)
    for (let d = cc + 1; d < n; d++) {
      const out = s[c.outputs[pairIndex(n, cc, d)]!]!;
      for (let a = 0; a < n; a++)
        for (let b = a + 1; b < n; b++) {
          const required = a !== cc && a !== d && b !== cc && b !== d;
          const present = has(out, pairIndex(n, a, b));
          if (present) nonzero++;
          if (present !== required) exact = false;
        }
    }

  const used = new Uint8Array(P + c.left.length);
  for (const o of c.outputs) used[o] = 1;
  for (let k = 0; k < c.left.length; k++) used[c.left[k]!] = used[c.right[k]!] = 1;
  let everyAdditionUsed = true;
  for (let k = 0; k < c.left.length; k++) if (!used[P + k]) everyAdditionUsed = false;

  return {
    n,
    additions: c.left.length,
    outputs: c.outputs.length,
    nonzeroCoefficients: nonzero,
    allAdditionsDisjoint,
    allOutputSupportsExact: exact,
    everyAdditionUsed,
  };
}
