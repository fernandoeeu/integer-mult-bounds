// PR 11 (Rohan Arun): "Record newly posted batched-network candidate and narrow
// comparisons". Head a97c1ba = PR 9's commit cfd6a2b + 004319c (research/geometric-dimensions/)
// + a97c1ba (eight README lines pointing to PR 10). No new multiplication exponent is
// claimed: "The current submitted conditional witness remains kappa = 3.8e-9".
// Source: research/geometric-dimensions/README.md.
//
// What is checkable as arithmetic:
//  (1) the dimension table: for each h, the estimated bit saving -log(1-eta)/log m from the
//      stated role count R (PR 7's interface formula at h), and the claim that exact upper
//      bounds reject every h != 28 against 761/10^11;
//  (2) the regular-graph degree d = C(r,t) C(h-r,r-t) > 0 for h >= 2r - t (Hall's condition);
//      the explicit bank matching for even h via a cyclic ordering of the edges of K_k
//      (built here by the README's insertion rule and checked on every five-set);
//  (3) the prime-power identity C(j,t) - [j=t] = [j=r] mod p for q = p^a, r = 2q-1, t = q-1,
//      the label pairing, and the exceptional h = r^2/t;
//  (4) the obstruction bounds: for q >= 7, eta <= 1/(2*20^3*1717) and a <= eta/((1-eta) log m)
//      < 761/10^11; for q = 5, R >= 2Q gives a < 761/10^11 for h = 15..29 (negative deficit
//      at h = 14) and for h >= 30 by a decreasing bound; the q = 4 target near h = 27.
// The producer counts R (h = 24..32) are taken as stated (h = 28 is entry 9's rebuilt
// count); rebuilding them is beyond this run's memory budget.

import { q, add, sub, mul, div, lt, le, ONE, ZERO, show, toDecimal, type Q } from "../rational";
import { binom } from "../intmath";
import { logIntegerEnclosure } from "../log";
import { savingEnclosure } from "../compact/ceiling";
import { primeFieldBitNetwork } from "./pr7";
import { equals, truth, cached, type Result } from "./rows";

const TEN = (k: number) => 10n ** BigInt(k);
const README = "PR11 research/geometric-dimensions/README.md";

export const STATED_PR11 = {
  table: [
    [24, 4728452n, "4.8281431"],
    [26, 7602157n, "7.2041450"],
    [27, 9476476n, "7.5484524"],
    [28, 11670540n, "7.6108867"],
    [29, 14398188n, "7.4068726"],
    [30, 17515487n, "7.1356570"],
    [32, 25224960n, "6.4700807"],
  ] as [number, bigint, string][],
  certified: q(761n, TEN(11)),
  matchingSizes: [8, 10, 24, 26, 28, 30],
  q4target: "4.04",
};

/** Cyclic order of the edges of K_k (k >= 3) with consecutive edges sharing one vertex (README insertion rule). */
export function edgeCycle(verts: number[]): [number, number][] {
  if (verts.length < 3) throw new Error("need k >= 3");
  const [x0, x1, x2] = verts as [number, number, number];
  let cyc: [number, number][] = [[x0, x1], [x1, x2], [x2, x0]];
  const old = [x0, x1, x2];
  for (const z of verts.slice(3)) {
    const e = cyc[0]!;
    const f = cyc[1]!;
    const a = e.find((x) => f.includes(x))!;
    const b = f.find((x) => x !== a)!;
    const middle = old.filter((x) => x !== a && x !== b).map((x) => [x, z] as [number, number]);
    cyc = [e, [a, z], ...middle, [b, z], ...cyc.slice(1)];
    old.push(z);
  }
  return cyc;
}

export function checkEdgeCycle(verts: number[]) {
  const c = edgeCycle(verts);
  const key = ([a, b]: [number, number]) => `${Math.min(a, b)},${Math.max(a, b)}`;
  const all = new Set(c.map(key));
  const k = verts.length;
  const adjacentShareOne = c.every((e, i) => {
    const f = c[(i + 1) % c.length]!;
    return e.filter((x) => f.includes(x)).length === 1;
  });
  return { ok: all.size === c.length && c.length === (k * (k - 1)) / 2 && adjacentShareOne, edges: c.length };
}

/** PR 7's paired matching with the Euler successor replaced by the insertion cycle; checked on every five-set. */
export function cycleMatching(h: number) {
  if (h % 2 !== 0) throw new Error("even h only");
  const P = h / 2;
  const succ = new Map<number, Map<string, [number, number]>>();
  for (let r = 0; r < P; r++) {
    const verts = [...Array(P).keys()].filter((x) => x !== r);
    const c = edgeCycle(verts);
    const m = new Map<string, [number, number]>();
    c.forEach(([a, b], i) => {
      const [x, y] = c[(i + 1) % c.length]!;
      m.set(`${Math.min(a, b)},${Math.max(a, b)}`, [Math.min(x, y), Math.max(x, y)]);
    });
    succ.set(r, m);
  }
  const pi = (pts: number[]): number[] => {
    const full: number[] = [];
    const single: number[] = [];
    for (let k = 0; k < P; k++) {
      const has0 = pts.includes(2 * k);
      const has1 = pts.includes(2 * k + 1);
      if (has0 && has1) full.push(k);
      else if (has0) single.push(2 * k);
      else if (has1) single.push(2 * k + 1);
    }
    if (full.length === 0) return single.map((x, i) => (i < 2 ? x : x ^ 1));
    if (full.length === 1) return [2 * full[0]!, 2 * full[0]! + 1, ...single.map((x) => x ^ 1)];
    const s = single[0]!;
    const [p, qq] = succ.get(s >> 1)!.get(`${full[0]},${full[1]}`)!;
    return [s ^ 1, 2 * p, 2 * p + 1, 2 * qq, 2 * qq + 1];
  };
  const seen = new Set<string>();
  let domain = 0;
  let allTwo = true;
  for (let a = 0; a < h; a++)
    for (let b = a + 1; b < h; b++)
      for (let c = b + 1; c < h; c++)
        for (let d = c + 1; d < h; d++)
          for (let e = d + 1; e < h; e++) {
            domain++;
            const T = [a, b, c, d, e];
            const U = pi(T).sort((x, y) => x - y);
            if (new Set(U).size !== 5) allTwo = false;
            if (T.filter((x) => U.includes(x)).length !== 2) allTwo = false;
            seen.add(U.join(","));
          }
  return { domain, distinct: seen.size, allTwo };
}

/** C(j,t) - [j=t] = [j=r] (mod p) for 0 <= j <= r, r = 2q - 1, t = q - 1. */
export function primePowerIdentity(p: bigint, q_: bigint) {
  const r = 2n * q_ - 1n;
  const t = q_ - 1n;
  for (let j = 0n; j <= r; j++) {
    const lhs = (((binom(j, t) - (j === t ? 1n : 0n)) % p) + p) % p;
    if (lhs !== (j === r ? 1n : 0n)) return false;
  }
  return true;
}

/** Saving upper bound a <= eta/((1-eta) log m) with log m from below. */
const aUpper = (eta: Q, m: bigint) => div(eta, mul(sub(ONE, eta), logIntegerEnclosure(m, 24).lower));

export function pr11(): { results: Result[]; values: Record<string, unknown> } {
  const out: Result[] = [];
  const OBS = "PR11-0 observations (no exponent is claimed)";
  const st = STATED_PR11;

  const SA = "PR11-A dimension table: estimated savings from the stated role counts (PR 7's interface at each h)";
  const rows = st.table.map(([h, R, dec]) => {
    const n = primeFieldBitNetwork(h, R);
    const enc = savingEnclosure(n.eta, logIntegerEnclosure(n.m, 24));
    return { h, R, dec, n, enc };
  });
  for (const r of rows) {
    // the stated decimal x 10^-9 must round the enclosure: |a* - dec| <= 5*10^-17
    const d = q(BigInt(r.dec.replace(".", "")), TEN(16));
    const half = q(5n, TEN(17));
    const okDigits = !lt(r.enc.upper, sub(d, half)) && !lt(add(d, half), r.enc.lower);
    if (r.h === 28)
      // the h = 28 row is PR 9's witness, not one of the six new screens (report.json has no h = 28 entry);
      // its digits differ in the last place from -log(1-eta)/log m, the formula of the other six rows
      out.push(truth("PR11-T stated decimals in the README", `ERRATUM README table, h = 28 row: "7.6108867" equals -log(1-eta)/log m to the stated digits`, README + " table (explore.py: -log1p(-eta)/log(m))", okDigits, `-log(1-eta)/log m = ${toDecimal(r.enc.lower, 17)}... rounds to 7.6108865e-9; 7.6108867 is eta/((1-eta) log m) = 7.6108867e-9 (an upper bound), so the row mixes formulas; no claim depends on it`, "observation"));
    else out.push(truth(SA, `h = ${r.h}, R = ${r.R}: saving ${r.dec}e-9 (enclosure within 5e-17 of the stated digits)`, README + " table", okDigits, `[${toDecimal(r.enc.lower, 17)}, ${toDecimal(r.enc.upper, 17)}]`));
    if (r.h !== 28) out.push(truth(SA, `h = ${r.h} is rejected against 761/10^11 (upper enclosure below)`, README, lt(r.enc.upper, st.certified), toDecimal(r.enc.upper, 14)));
    out.push(equals(SA, `h = ${r.h}: q = C(h-2,3) C(h,2) + C(h,2) <= R (output uses alone)`, README, BigInt(binom(r.h - 2, 3) * binom(r.h, 2) + binom(r.h, 2)) <= r.R ? "yes" : "no", "yes", "identity"));
  }
  out.push(equals(SA, "h = 28 row equals PR 9's R = 11670540 (rebuilt in entry 9)", README, st.table[3]![1], 11670540n, "identity"));

  const SB = "PR11-B bank matching: Hall degree and the explicit cycle construction for even h";
  for (const h of [8, 9, 10, 27, 29, 30]) out.push(truth(SB, `degree C(5,2) C(h-5,3) > 0 at h = ${h} (h >= 2r - t = 8)`, README, binom(5, 2) * binom(h - 5, 3) > 0n, `${binom(5, 2) * binom(h - 5, 3)}`, "identity"));
  for (const k of [3, 4, 5, 9, 12, 13, 14]) {
    const c = checkEdgeCycle([...Array(k).keys()]);
    out.push(truth(SB, `insertion rule gives a cyclic edge order of K_${k} with consecutive edges sharing one vertex`, README, c.ok, `${c.edges} edges`));
  }
  for (const h of st.matchingSizes) {
    const m = cached(`pr11 match ${h}`, () => cycleMatching(h));
    out.push(truth(SB, `h = ${h}: the cycle matching is a bijection of the C(h,5) five-sets with |T cap pi(T)| = 2`, README + " (matching.py checks h = 8, 10, 24, 26, 28, 30, 32)", m.allTwo && m.distinct === m.domain && BigInt(m.domain) === binom(h, 5), `${m.distinct} images`));
  }

  const SC = "PR11-C prime-power family: scalar identity, labels, exceptional dimension";
  const pps: [bigint, bigint][] = [[2n, 2n], [3n, 3n], [2n, 4n], [5n, 5n], [7n, 7n], [2n, 8n], [3n, 9n], [11n, 11n], [2n, 16n], [5n, 25n], [3n, 27n]];
  for (const [p, qq] of pps) out.push(truth(SC, `C(j,${qq - 1n}) - [j=${qq - 1n}] = [j=${2n * qq - 1n}] mod ${p}, j = 0..${2n * qq - 1n}`, README, primePowerIdentity(p, qq), "", "constant"));
  out.push(truth(SC, "the identity fails for the non-prime-power q = 6 in every characteristic p | 6 (control)", "derived", !primePowerIdentity(2n, 6n) && !primePowerIdentity(3n, 6n), "", "observation"));
  out.push(truth(SC, "pairing <t_S,t_T> = |S cap T| - t r^2/r^2 and norm r - t = q (form I - (t/r^2) J)", README, [2n, 3n, 4n, 5n, 7n].every((qq) => 2n * qq - 1n - (qq - 1n) === qq), "", "identity"));
  let exc = true;
  for (let qq = 2n; qq <= 2000n; qq++) if ((2n * qq - 1n) ** 2n % (qq - 1n) === 0n && qq !== 2n) exc = false;
  out.push(truth(SC, "h = r^2/t is an integer only at q = 2 (h = 9) for 2 <= q <= 2000", README, exc && 9n % 1n === 0n && (3n * 3n) / 1n === 9n, ""));

  const SD = "PR11-D obstruction bounds against 761/10^11 (retained-center architecture, c + Q compiler)";
  const target = st.certified;
  const C137 = binom(13, 6);
  const eta7 = q(1n, 2n * 20n ** 3n * 1717n);
  out.push(
    equals(SD, "C(2q-1, q-1) at q = 7", README, C137, 1716n),
    truth(SD, "Q >= v C(r,t) (C(h,t)C(h-t,q) = C(h,r)C(r,t)), so eta <= 1/(2h^3(1 + C(r,t))) (checked at q = 7, h = 20..40)", README, [...Array(21).keys()].every((i) => {
      const h = BigInt(20 + i);
      return binom(h, 6n) * binom(h - 6n, 7n) === binom(h, 13n) * binom(13n, 6n);
    }), "", "identity"),
    truth(SD, "q >= 7: a <= eta/((1-eta) log 8000) < 761/10^11 with eta = 1/(2*20^3*1717)", README, lt(aUpper(eta7, 8000n), target), toDecimal(aUpper(eta7, 8000n), 14)),
  );
  // q = 5: r = 9, t = 4, Q = C(h,4)(C(h-4,5) + 1), R >= 2Q
  const q5 = (h: bigint) => {
    const v = binom(h, 9n);
    const Q = binom(h, 4n) * (binom(h - 4n, 5n) + 1n);
    const num = v - 6n * binom(h, 4n) * (h - 4n);
    return { v, Q, num, eta: num > 0n ? q(num, 2n * h ** 3n * (v + 2n * Q)) : null };
  };
  out.push(truth(SD, "q = 5, h = 14 = 3q - 1: the deficit numerator v - 6 C(h,4)(h-4) is negative", README, q5(14n).num < 0n, `${q5(14n).num}`));
  let all5 = true;
  let worst = ZERO;
  for (let h = 15n; h <= 29n; h++) {
    const r = q5(h);
    if (!r.eta) continue;
    const u = aUpper(r.eta, h ** 3n);
    if (!lt(u, target)) all5 = false;
    if (lt(worst, u)) worst = u;
  }
  out.push(truth(SD, "q = 5, h = 15..29: a <= eta/((1-eta) log m) < 761/10^11 with R >= 2Q", README, all5, `largest bound ${toDecimal(worst, 14)}`));
  const eta30 = q(1n, 2n * 30n ** 3n * (1n + 2n * binom(9n, 4n)));
  out.push(truth(SD, "q = 5, h >= 30: eta <= 1/(2h^3(1 + 2 C(9,4))) (decreasing in h), bound at h = 30 below 761/10^11", README, lt(aUpper(eta30, 27000n), target), toDecimal(aUpper(eta30, 27000n), 14)));
  // q = 4 target near h = 27: r = 7, t = 3; largest c/Q with -log(1-eta)/log m > 761/10^11
  const h = 27n;
  const v = binom(h, 7n);
  const Q = binom(h, 3n) * (binom(h - 3n, 4n) + 1n);
  const num = v - 6n * binom(h, 3n) * (h - 3n);
  const L = logIntegerEnclosure(h ** 3n, 24);
  // eta > a L.upper suffices; eta = num/(2h^3(v + c + Q)) > a L  <=>  v + c + Q < num/(2h^3 a L)
  const cMax = sub(div(q(num), mul(q(2n * h ** 3n), mul(target, L.upper))), q(v + Q));
  out.push(truth(OBS, "q = 4 at h = 27: additions per designated output c/Q that would still beat 761/10^11", README + ": roughly fewer than 4.04", true, `c/Q < ${toDecimal(div(cMax, q(Q)), 4)}`, "observation"));
  out.push(truth(OBS, "the table's producer counts for h != 28 are taken as stated (not rebuilt here)", README, true, "", "observation"));
  const ordered = [...out.filter((r) => r.section !== OBS), ...out.filter((r) => r.section === OBS)];
  return { results: ordered, values: { rows: rows.map((r) => ({ h: r.h, R: r.R, lower: r.enc.lower, upper: r.enc.upper })), q4: div(cMax, q(Q)) } };
}
