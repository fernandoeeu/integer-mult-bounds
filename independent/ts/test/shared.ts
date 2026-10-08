// The h = 50 circuit build and verification takes about ten seconds. The runner and
// compare tests share one build (bun runs all test files in one process).
import { computeBit, STATED_BIT, type BitValues } from "../src/checks";

let cache: BitValues | undefined;

/** Bit-network values for the published conventions (no second, alternative build). */
export function bitValues(): BitValues {
  cache ??= { ...computeBit({ alternative: false }), L0: STATED_BIT.L0 };
  return cache;
}
