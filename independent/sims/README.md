# Counterexample hunts by simulation (7 and 8 October 2026)

Independent small-size simulations of the finite constructions behind the compact-control witness at commit 6e56487 and behind outside pull requests 2 to 16. Each folder implements a construction from its written notes, independently of the repository's Python wherever possible, and tries to break the finite claims the notes make: exhaustively at small sizes, with adversarial and random inputs at larger ones, and at the claimed sizes where feasible. Every pass or fail decision uses exact arithmetic (integers, rationals, finite fields, or certified ball arithmetic).

**Result: no counterexample was found in any construction.** A few textual issues were found; none changes a claimed bound (see "Findings").

Caution: not finding a counterexample is not a proof. These runs test finite instances; the asymptotic and analytic steps of every argument, the fixed-tape cost accounting, and the upstream OpenAI manuscript are not checked. Every result here stays conditional, as the repository says.

## Folders

| folder | target (pinned) | what was tested | result |
| --- | --- | --- | --- |
| `address-maps/` | head 6e56487, compact-control movement | packed modular address maps and inverses, four-update identity, bad set and repair, field order; about 339 million addresses exhaustively | no failure |
| `dirty-repair/` | head 6e56487 | dirty compact controls with arbitrary initial temporaries; deterministic exceptional repair; the bad-fraction bound 5/(128 p^3); about 1.18 billion addresses exhaustively | no failure; the bound is tight (ratio up to 0.99976) |
| `rotation/` | head 6e56487, `lem:record-paid-rotation` | two-piece streaming rotation on an explicit tape model: correctness and every stated count (cell writes, fibers per record, offset and counter work) | no failure; one unstated hypothesis (see Findings) |
| `layout/` | head 6e56487, compact-control layout | recursive layout invariant: reserved ranges, carving, padding, row splitting, stopping, piece decomposition; record-level simulation with dirty padded rows | no failure; one wording issue (see Findings) |
| `pr2-aligned/` | PR 2 head 1c200af | aligned paired bit circuit at h = 50: counts, exact outputs, disjointness, common point, frames, role compilation, scalar schedule; exact linear algebra at small h | no failure; graph identical to the PR's node by node |
| `pr3-pr4-complex/` | PR 3 dfe5b81, PR 4 42a88ef | compressed and retained complex circuits: exact side maps, F_2 labels and frames, tensor-level frames and phases at small h, dirty-scratch scalar runs, three-stage exchange, stage sharing | no failure |
| `pr5-gaussian/` | PR 5 d3d370c | fast Gaussian resampling: E formula, step identity, path bound, power bound, Neumann count, chirp identity, fixed-point block algorithm with precision accounting (Arb balls) | no failure of the argument; one false literal constant (see Findings) |
| `round2-circuits/` | PR 6 5015011, PR 4 8c225e6 | aligned bit circuit with cheaper centers; retained totals with PR 3's shared exclusions | no failure |
| `round3/` | PR 7 6725c6a, PR 8 9454645 | F_3 five-subset bit network at h = 28 (C++ support verifier, 11.24 million nodes) and paired complex producer; geometric complex network at n = 25 | no failure |
| `round4a/` | PR 9 cfd6a2b, PR 13 3ef246f | refined star templates at h = 28; auxiliary source frames (endpoint identity, exit idempotent, basis lemma at small h) | no failure |
| `round4b/` | PR 10 62691e3, PR 11 a97c1ba, PR 12 35d31e3 | batched recursive networks: pivot profile, controlled basis, end-to-end batched recursion against exact chunk swaps, complex bulk identity | no failure |
| `round5/` | PR 14 1fa5b9a, PR 15 a17cab3, PR 16 a80f5e6 | source frames combined with batching: one shared basis against every claimed pivot profile (h = 4 to 7, real label forms), nested basis exit block, bit and complex moments, guard bound | no failure; PR 15 and PR 16 disagree on a finite edge list (see Findings) |

Each folder has a `run_all.sh`. Scripts that compare against the repository or the pull requests read a clone from the environment variable `REPO` (a clone of CrocSwap/integer-mult-bounds with pull requests fetched as `prs/N`, for example `git fetch origin '+refs/pull/*/head:refs/remotes/prs/*'`). Scratch checkouts of pull requests, generated binaries and large generated data are not included; the scripts recreate them. Logs from the original runs are kept under each folder's `logs/` or `results/`.

## Findings

None of these refutes a claim; each is a place where a text could be tightened.

1. **`lem:record-paid-rotation` (head, `notes/compact-control-movement.tex`):** the fiber count "every fiber contains at least one complete record" needs the records to lie in the suffix after the target field. The lemma states only "M records of R bits". The application satisfies this; the hypothesis is not written down. (`rotation/`)
2. **Layout padding (head, `notes/compact-control-layout.tex`):** the text says padding "increases total volume by at most two"; the upstream sentence it replaces says "by a factor at most two". The factor reading holds; the additive one does not. (`layout/`)
3. **PR 5, Lemma chirped-gaussian:** the stated input error bound 2^(4-P) F with F = e^(pi alpha^2 / 4) is false for alpha >= 21, because the shift by ceil(1.14 alpha^2) and pi/(4 ln 2) < 1.14. Taking F = 2^ceil(1.14 alpha^2) repairs it, and the precision P = 34p absorbs the change; the final errors stay below 0.7 * 2^-p. Reproduction: `pr5-gaussian/repro_f_constant.py`. (`pr5-gaussian/`)
4. **PR 15 versus PR 16, the h = 28 complex edge list:** both call their rank histogram a complete physical edge list, but they differ in shape (PR 15 has N = v^3 more edges of ranks 27 and 729 and N fewer of rank 756; the rank sums agree). The cause is where the first source copy sits at the inverse middle stage (frame a-1 in PR 15, which matches the upstream table in 03-motifs.tex; the low frame in PR 16's note). Both complex savings certify under either list, so neither claim changes. (`round5/pr16chk/cmp_hist.py`)
5. **Unstated orders.** Several notes leave summation or creation orders open (the paired circuit's balanced split and zero terms, PR 4's rectangle plan, PR 6's zero terms, PR 7's context order, PR 9's tie rule); counts reproduce only with the scripts' choices. The arithmetic re-check (branch `review/open-prs`, `independent/ts/prs/REPORT.md`) quantifies each.

## Disclosure

All code, tests and this README were written by Claude (an AI model by Anthropic) in Claude Code sessions directed by @fernandoeeu, a software engineer who is not a specialist in this mathematics. Separate agent sessions wrote each hunt. That is not independent review: no human has audited these simulations. Contributed under the repository's Apache-2.0 license.
