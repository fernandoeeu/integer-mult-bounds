// Row helpers for the PR checks. They produce the same `Result` rows as
// src/checks.ts (same kinds, same counting rules), so src/prs/main.ts prints
// and counts them the same way `bun run check` does.

import { type Q, show } from "../rational";
import { holds, slack, type Check } from "../parameters";
import type { Kind, Result } from "../checks";

export type { Kind, Result };

export function fromCheck(section: string, k: Check): Result {
  return { section, name: k.name, source: k.source, ok: holds(k), detail: `slack ${show(slack(k))}`, kind: k.kind ?? "check" };
}

/** A recomputed value against the number a PR's note states. */
export function equals(section: string, name: string, source: string, got: bigint | Q | number | string, expected: bigint | Q | number | string, kind: Kind = "check"): Result {
  const g = typeof got === "object" ? show(got) : `${got}`;
  const e = typeof expected === "object" ? show(expected) : `${expected}`;
  return { section, name, source, ok: g === e, detail: g === e ? g : `got ${g}, note says ${e}`, kind };
}

export function truth(section: string, name: string, source: string, ok: boolean, detail = "", kind: Kind = "check"): Result {
  return { section, name, source, ok, detail, kind };
}

/** Rows that are counted and decide a verdict (same rule as src/checks.ts). */
export const counted = (r: Result) => r.kind === "check" || r.kind === "condition" || r.kind === "constant" || r.kind === "sample";

/** Memoize expensive, parameter-light computations within one process. */
const memo = new Map<string, unknown>();
export function cached<T>(key: string, f: () => T): T {
  if (!memo.has(key)) memo.set(key, f());
  return memo.get(key) as T;
}
