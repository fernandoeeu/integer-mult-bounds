// The exact arithmetic itself, tested against identities with known closed forms.
import { describe, expect, test } from "bun:test";
import { q, add, sub, mul, div, pow, cmp, eq, show, parseQ, sum, twoPow, ONE, ZERO, lt } from "../src/rational";
import { binom, floorRoot, ceilRoot, floorLog2 } from "../src/intmath";
import { logEnclosureNearOne, logIntegerEnclosure, expLowerBound } from "../src/log";
import { parseLossless } from "../src/comparator";

// small deterministic generator, so failures are reproducible
function rng(seed: number) {
  let x = seed >>> 0;
  return () => ((x = (Math.imul(x, 1664525) + 1013904223) >>> 0) / 2 ** 32);
}
const randQ = (r: () => number) => q(BigInt(Math.floor(r() * 2e6) - 1e6), BigInt(Math.floor(r() * 1e6) + 1));

describe("rational normal form and field identities", () => {
  test("normal form: positive denominator, reduced", () => {
    expect(show(q(6n, -4n))).toBe("-3/2");
    expect(show(q(0n, -7n))).toBe("0");
    expect(eq(q(10n, 20n), q(1n, 2n))).toBe(true);
    expect(() => q(1n, 0n)).toThrow();
    expect(() => div(ONE, ZERO)).toThrow();
  });

  test("parse/show round trip, including the certificate's 2^-59", () => {
    for (const s of ["1/576460752303423488", "-3/7", "272158569/156250000000000000000000000", "0", "125000"])
      expect(show(parseQ(s))).toBe(s);
    expect(eq(twoPow(-59), parseQ("1/576460752303423488"))).toBe(true);
  });

  test("ring identities on random rationals", () => {
    const r = rng(7);
    for (let i = 0; i < 300; i++) {
      const [x, y, z] = [randQ(r), randQ(r), randQ(r)];
      expect(eq(mul(add(x, y), add(x, y)), add(add(mul(x, x), mul(q(2n), mul(x, y))), mul(y, y)))).toBe(true);
      expect(eq(mul(x, add(y, z)), add(mul(x, y), mul(x, z)))).toBe(true);
      expect(eq(sub(add(x, y), y), x)).toBe(true);
      if (y.num !== 0n) expect(eq(mul(div(x, y), y), x)).toBe(true);
      expect(cmp(x, y)).toBe(-cmp(y, x) as -1 | 0 | 1);
    }
  });

  test("telescoping sum: sum_{k=1}^n 1/(k(k+1)) = n/(n+1)", () => {
    for (const n of [1, 2, 10, 100]) {
      const s = sum([...Array(n).keys()].map((k) => q(1n, BigInt((k + 1) * (k + 2)))));
      expect(eq(s, q(BigInt(n), BigInt(n + 1)))).toBe(true);
    }
  });

  test("geometric sum: sum_{k=0}^n 2^-k = 2 - 2^-n, and pow with negative exponents", () => {
    for (const n of [0, 1, 5, 64]) {
      const s = sum([...Array(n + 1).keys()].map((k) => twoPow(-k)));
      expect(eq(s, sub(q(2n), twoPow(-n)))).toBe(true);
    }
    expect(eq(pow(q(2n, 3n), -3), q(27n, 8n))).toBe(true);
  });
});

describe("integer helpers", () => {
  test("binomial coefficients: Pascal's rule and C(50,3) = 19600", () => {
    for (let n = 1; n < 40; n++) for (let k = 1; k < n; k++) expect(binom(n, k)).toBe(binom(n - 1, k - 1) + binom(n - 1, k));
    expect(binom(50, 3)).toBe(19600n);
    expect(binom(47, 2)).toBe(1081n);
  });

  test("floorRoot(x,k)^k <= x < (floorRoot(x,k)+1)^k, ceilRoot dual", () => {
    const r = rng(11);
    for (let i = 0; i < 300; i++) {
      const x = BigInt(Math.floor(r() * 1e9)) * BigInt(Math.floor(r() * 1e9)) + BigInt(i);
      for (const k of [2, 3, 4, 7]) {
        const f = floorRoot(x, k);
        const K = BigInt(k);
        expect(f ** K <= x && x < (f + 1n) ** K).toBe(true);
        const c = ceilRoot(x, k);
        expect(c ** K >= x && (c === 0n || (c - 1n) ** K < x)).toBe(true);
      }
    }
    expect(floorRoot(10n ** 40n, 4)).toBe(10n ** 10n);
    expect(floorLog2(125000n)).toBe(16);
  });
});

describe("logarithm enclosures (atanh series with tail bound)", () => {
  test("log 2 enclosure contains 0.693147180559945309417232121458...", () => {
    const e = logEnclosureNearOne(q(2n));
    expect(lt(e.lower, q(693147180559945309417233n, 10n ** 24n))).toBe(true);
    expect(lt(q(693147180559945309417232n, 10n ** 24n), e.upper)).toBe(true);
  });

  test("enclosures are consistent with log(xy) = log x + log y", () => {
    for (const [a, b] of [
      [3n, 7n],
      [125000n, 8n],
      [999n, 1001n],
    ] as const) {
      const ab = logIntegerEnclosure(a * b);
      const ea = logIntegerEnclosure(a);
      const eb = logIntegerEnclosure(b);
      // the two intervals for log(ab) must overlap
      expect(lt(ab.lower, add(ea.upper, eb.upper)) && lt(add(ea.lower, eb.lower), ab.upper)).toBe(true);
    }
  });

  test("more series terms never loosen the enclosure", () => {
    const x = q(15625n, 8192n); // m / 2^16 for m = 125000
    const a = logEnclosureNearOne(x, 10);
    const b = logEnclosureNearOne(x, 24);
    expect(cmp(a.lower, b.lower) <= 0 && cmp(b.upper, a.upper) <= 0).toBe(true);
  });

  test("failure mode: L0 cannot be lowered to 11736/1000 (log 125000 > 11.736)", () => {
    const e = logIntegerEnclosure(125000n);
    expect(lt(e.upper, q(11737n, 1000n))).toBe(true);
    expect(lt(q(11736n, 1000n), e.lower)).toBe(true);
  });

  test("exp lower bound: e^11.737 > 125000 is provable, e^11.736 > 125000 is not", () => {
    expect(lt(q(125000n), expLowerBound(q(11737n, 1000n), 80))).toBe(true);
    for (const K of [40, 80, 120]) expect(lt(expLowerBound(q(11736n, 1000n), K), q(125000n))).toBe(true);
  });
});

describe("certificate parsing", () => {
  test("failure mode avoided: JSON.parse rounds a 44-digit integer, the lossless parser keeps it", () => {
    const text = '{"E": 12908648646364723556470023518520280006040064, "r": "1/3", "ok": true, "xs": [1, -2]}';
    expect(String((JSON.parse(text) as { E: number }).E)).not.toBe("12908648646364723556470023518520280006040064");
    const o = parseLossless(text) as { E: string; r: string; ok: boolean; xs: string[] };
    expect(o.E).toBe("12908648646364723556470023518520280006040064");
    expect([o.r, o.ok, o.xs.join(",")]).toEqual(["1/3", true, "1,-2"]);
    expect(() => parseLossless('{"x": 1.5}')).toThrow();
  });
});
