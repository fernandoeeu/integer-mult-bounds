// The rational form I - J/9 and the stage-1/stage-3 auxiliary matching pi.
//
// Sources: upstream 03-motifs.tex (form I - J/9 on F = Q^h, exceptional
// eigenvalue 1 - h/9, triple norm 2) and paired-construction.tex, subsection
// "Reversible roles and frames in both directions":
//   "pi is a bijection of triples with |T cap pi(T)| = 1: pair consecutive
//    ground points; for a triple with a full pair and singleton, keep the
//    singleton and cycle the full pair among pairs not containing it;
//    otherwise keep the point in the least indexed pair and flip the other two
//    to their partners."
// The joining labels E = F (x) <t_A> (x) <t_B> and H = <t_B (x) t_pi(A)>^perp (x) F
// satisfy E within H exactly when <t_A, t_pi(A)> = 0, i.e. |A cap pi(A)| = 1.

import { type Q, q, sub, mul, add, ZERO, eq } from "./rational";

/** <x,y> for the form I - J/9: sum x_j y_j - (sum x)(sum y)/9. */
export function form(x: Q[], y: Q[]): Q {
  let dot = ZERO;
  let sx = ZERO;
  let sy = ZERO;
  for (let j = 0; j < x.length; j++) {
    dot = add(dot, mul(x[j]!, y[j]!));
    sx = add(sx, x[j]!);
    sy = add(sy, y[j]!);
  }
  return sub(dot, mul(mul(sx, sy), q(1n, 9n)));
}

export function indicator(h: number, pts: number[]): Q[] {
  const v = new Array<Q>(h).fill(ZERO);
  for (const p of pts) v[p] = q(1n);
  return v;
}

/** Exceptional eigenvalue of I - J/9 on Q^h (eigenvector all-ones): 1 - h/9. */
export const exceptionalEigenvalue = (h: number) => sub(q(1n), q(BigInt(h), 9n));

/** pi on a sorted triple of [h], h even; ground pairs are {2t, 2t+1}. */
export function piMatching(h: number, T: number[]): number[] {
  if (h % 2 !== 0) throw new Error("pi is defined here for even h");
  const pairOf = (x: number) => x >> 1;
  const partner = (x: number) => x ^ 1;
  const [x, y, z] = T as [number, number, number];
  const pairs = [pairOf(x), pairOf(y), pairOf(z)];
  // a full pair plus a singleton
  for (const [p1, p2, s] of [
    [x, y, z],
    [x, z, y],
    [y, z, x],
  ] as const) {
    if (pairOf(p1) === pairOf(p2)) {
      const allowed = [...Array(h / 2).keys()].filter((t) => t !== pairOf(s));
      const next = allowed[(allowed.indexOf(pairOf(p1)) + 1) % allowed.length]!;
      return [s, 2 * next, 2 * next + 1].sort((a, b) => a - b);
    }
  }
  // three different pairs: keep the point in the least indexed pair
  const keepIdx = pairs.indexOf(Math.min(...pairs));
  return T.map((p, i) => (i === keepIdx ? p : partner(p))).sort((a, b) => a - b);
}

/** Is U a 3-element subset of [h], listed in increasing order? */
function isSortedTriple(h: number, U: number[]): boolean {
  return U.length === 3 && U.every((p) => Number.isInteger(p) && 0 <= p && p < h) && U[0]! < U[1]! && U[1]! < U[2]!;
}

/**
 * Checks a candidate matching `pi` (default: the note's pi) on all triples of [h]:
 *  - bijective: every image is a triple and no two triples share an image
 *    (a map from a finite set to itself is a bijection iff it is injective);
 *  - intersectionOne: |A cap pi(A)| = 1 for every triple A;
 *  - joiningLabelsNested: <t_A, t_pi(A)> = 0 in the form I - J/9, i.e. E within H.
 */
export function checkMatching(h: number, pi: (T: number[]) => number[] = (T) => piMatching(h, T)) {
  const triples: number[][] = [];
  for (let x = 0; x < h; x++) for (let y = x + 1; y < h; y++) for (let z = y + 1; z < h; z++) triples.push([x, y, z]);
  const seen = new Set<string>();
  let imagesAreTriples = true;
  let intersectionOne = true;
  let orthogonal = true;
  for (const T of triples) {
    const U = pi(T);
    if (!isSortedTriple(h, U)) imagesAreTriples = false;
    seen.add(U.join(","));
    if (T.filter((p) => U.includes(p)).length !== 1) intersectionOne = false;
    if (!eq(form(indicator(h, T), indicator(h, U)), ZERO)) orthogonal = false; // <t_A, t_pi(A)> = 0
  }
  return {
    triples: triples.length,
    bijective: imagesAreTriples && seen.size === triples.length,
    intersectionOne,
    joiningLabelsNested: orthogonal,
  };
}
