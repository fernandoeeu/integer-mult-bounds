# Re-check of four outside pull requests (7 October 2026)

Scope: the arithmetic of four outside PRs to CrocSwap/integer-mult-bounds: the counts that feed each witness, derived network quantities, log enclosures, every parameter inequality, the margins and the final strict comparison with the claimed kappa. Circuit validity (labels, frames, schedules, phases) was reviewed separately by simulation (see `independent/sims/` on the `review/finite-sims` branch) and is not covered here, except where a count required rebuilding the circuit. All recomputation is exact (BigInt rationals, no floating point in any decision), as an extension of the independent TypeScript checker. Each PR's JSON certificate was used only at the end, for a field-by-field comparison.

Caution: a passing row means a finite arithmetic statement or count holds. It is not a review of the written proofs; every PR remains conditional on the unverified upstream manuscript and the repository's written extensions.

PR heads checked: prs/1 bfb168a, prs/2 1c200af, prs/3 dfe5b81, prs/4 42a88ef. Base of the repository: 6e56487. PR 4's later head 8c225e6 and PRs 5 and 6 are covered in the addendum of 8 October below.

## Summary

| PR | author, base | claim | verdict | key recomputed numbers |
| --- | --- | --- | --- | --- |
| 1 | Aurel Prosz, bcd4ebd | kappa = 17523184/10^25 by retuning beta, eps, delta of the 2^-59 witness | holds | G = g2 = g3 = 1.7523184646864326407676563456e-18 exactly; gap 6.46864326407676563456e-26; scoped supremum 1.752318464688658510620071066e-18 |
| 2 | Andrew Barnes, bcd4ebd | aligned labelling: c = 435450, R = 494250, a = 305/10^11, kappa = 17*2^-63 | holds | c = 435450 rebuilt (two derivations); eta_b = 23/642375000; G = 739738521/(4*10^26) |
| 3 | eumemic, 6e56487 | compressed complex side circuit: R = 108195, a_c = 14/10^9, kappa = 59/10^11 | holds | circuit rebuilt: 80595 additions, 27600 pieces, side map exact; eta_c = 28/205789375; G_* = 14779261/(25*10^15) |
| 4 | David Leen, 6e56487 (head 42a88ef) | retained-total complex motif at h = 24: R_aux = 365760, a_c = 750/10^11, kappa = 591/10^12 | holds; gap in the text (rectangle plan not fully specified) | 329811 rectangle roles reproduced with the first-candidate tie rule; eta = 365/5084246016; G_* = 2956521/(5*10^15) |

No recomputed number disagrees with any note or certificate (`compare:prs`: 0 differing fields over 493 leaves).

The one point for an author: PR 4's note does not say how the "selected" rectangle plan breaks ties or where the ground set is split. Keeping the first cheapest candidate (the order its Python uses) gives 329811 roles, as stated. Keeping the last cheapest candidate gives 349394 roles, and then only 714/10^11 is certified, below the claimed 750/10^11. The claimed plan exists and is verified (an exact partition with the stated counts), so the claim holds, but the count cannot be reproduced from the text alone.

## Commands (from independent/ts, Bun 1.4.2)

    bun run check:prs                 # all four PRs, one verdict each; exit 0 iff all hold
    bun run check:prs --only=3        # one PR
    bun run check:prs --observation   # also PR 2 under the other reading of the circuit prose
    bun run check:prs --set=pr4.kappa=2956521/5000000000000000
    bun run compare:prs               # field-by-field comparison with the four certificates
    PR_CLONE=<clone with commit 42a88ef> bun run compare:prs   # also recompute PR 4's proof_sha256 hashes
    bun test                          # includes test/prs/

Tails: `check:prs` about 55 s; PR1 27 checks + 35 conditions + 3 constants, PR2 37 + 33 + 2, PR3 47 + 44 + 3, PR4 41 + 43 + 1, all 0 failed; VERDICT PR1..PR4: PASS. `compare:prs`: PR1 150 leaves (71 recomputed, 55 inputs, 5 other method, 19 not compared, 0 differ); PR2 127 (73, 37, 2, 15, 0); PR3 111 (67, 33, 2, 9, 0); PR4 105 (60, 33, 2, 10, 0; without PR_CLONE the six proof_sha256 fields are not compared); "COMPARE PRs: no disagreement". Existing commands unchanged: `bun run check` (both PASS), `bun run compare` (no disagreement), `bun test` 407 pass / 0 fail.

## PR 1: tuned parameters of the paired witness

Claim: networks unchanged (a = 296/10^11, b = a_c = 1/10^11, h = 50). The 2^-59 witness's downstream parameters move to the edge: beta = 99999912384/10^11, eps = 1999999999999/10^13, delta = 10^-14, C1 = 2, recipe c = beta a, lambda = 1 - (1+beta)a^2/2, lambda' = 1 - beta a^2, kappa = 17523184/10^25. Also a scoped supremum G_* = z_*/(5+4z_*) and an unachieved design target (R <= 356295 for a = 417/10^11).

Recomputed (`src/prs/pr1.ts`): the 29 conditions of the 2^-59 system, the seven margins, G and kappa < G; the stated decimals (all exact); the guard at the new beta (E, B, C0, 5 - 4beta <= 7/5, 7/5 + 1/2 <= C1); the Gaussian width by rigorous log enclosures (the note's d^(10^13) <= b^1999999999999 is not computable directly); the supremum by an integer square root of the discriminant (the PR bisects), matching the stated digits, with kappa above 99.999996% of G_*; the design target (maxSideRoles = 356295) as an observation. The three "delicate" recurrence gaps in the text are identities of the recipe and are labelled so.

Context: base bcd4ebd. The document compares with 2^-59, while the head's witness is 83/10^12, about 4.7*10^7 times larger. With PR 2's a = 305/10^11, PR 1's beta fails the leaf condition.

## PR 2: aligned paired circuits

Claim: same local circuit (9813 additions). New labelling per common point i: points other than i and i XOR 1 increasing, then i XOR 1. Root pairs agree across groups and more fixed-pair sums merge: c = 435450 (14944 fewer), q = 58800, R = 494250, eta_b = 23/642375000, certifying a = 305/10^11, and G = 739738521/(4*10^26) > 17*2^-63.

Recomputed (`src/prs/aligned.ts`, `pr2.ts`): the merge generalised to any labelling (the standard labelling still gives 450394 / 40256); aligned c = 435450 with 55200 merged and 0 pruned; a second count by support hashing; W, s, D, eta_b; log m by two routes; role budget 494347 (97 spare); a = 306/10^11 would need R <= 492667; parameters, G, guard, Gaussian and fixed-network ceiling.

Observation: under the other reading of the circuit prose (ceiling split, zeros dropped, weights first) the aligned graph has R = 494100; it still certifies only 305.

Context: at the head the complex network binds, so this bit saving alone does not raise kappa; it matters together with PR 3 or PR 4.

## PR 3: compressed complex circuit

Claim: the complex motif at h = 25 keeps central wires and frames; its 3693800 side wires per invocation become a shared-sum circuit: 80595 additions, 27600 pieces, 12 per target, R = 108195, eta_c = 28/205789375, a_c = 14/10^9; the bit network then binds and kappa = 59/10^11.

Recomputed (`src/prs/complexCircuit.ts`, `pr3.ts`, built from the construction note only; the Python was not read): the counts, the side map exact on 3693800 coefficients, both orders of the region additions; W_c, L_c, s_c, eta_c; log m_c by two routes (slack about 0.6%); the gate bound; the generalized guard; all compact conditions; G_* = g3 = 14779261/(25*10^15), gap 29261/(25*10^15); 2^-31 < kappa < 2^-30; tightest condition tau < lambda with slack 1/(5*10^11); ceiling kappa < a/5 with kappa above 99.6% of it.

## PR 4: retained complex totals at h = 24 (head 42a88ef)

Claim: a new complex motif at h = 24 with a rectangle partition of disjoint pairs, fixed-pair trees and h retained totals instead of central wires: 329811 rectangle roles, q_2 = 27600, C = 132180, q = 233580, R_aux = 365760, eta = 365/5084246016, a_c = 750/10^11, kappa = 591/10^12.

Recomputed (`src/prs/retained.ts`, `pr4.ts`): the cheapest plan in the note's family (first cheapest kept on ties), 329811 roles; its 18593 rectangles partition all 2691920 disjoint pairs exactly; after repair 123855 additions and 205956 outputs; pair trees, C, q, R_aux, W, L_loss, s, eta; log m by two routes; exact slack 11935523/49650840000000000; largest grid saving 752; guard, recurrence, compact conditions; G_* = g3 = 2956521/(5*10^15), gap 1521/(5*10^15); tightest tau < lambda with slack 10^-12; proof_sha256 of six files recomputed.

Gap in the text: ties and split points are not fixed (see the summary). Observation: 4833 of 18719 rectangles repeat a source family; sharing them would save 40935 additions.

## Cross-PR (speculation only, never part of a verdict)

- PR 3 and PR 4 compete for the same slot; both end within 0.2% of a/5 = 5.92e-10.
- PR 2's a = 305/10^11 would raise that to 6.10e-10. A candidate kappa = 609/10^12 passes all compact conditions with either complex network, assuming the compact construction accepts PR 2's network unchanged.

## Independence caveats

- PR 2: `aligned_paired_network.py` and the `shared_point_circuit.py` diff were read before writing the code.
- PR 3: built from the note only.
- PR 4: `best_plan` was read before writing the plan search; partition, repair and counts are checked independently.
- Certificates were opened early to learn their structure; no certificate value feeds a check.

# Addendum (8 October 2026): PR 4 head 8c225e6, PR 5 and PR 6

Same scope and caution as above: the arithmetic only (counts feeding each witness, derived network quantities, log enclosures, every parameter inequality, margins, the minimum and the strict comparison with kappa), exact BigInt rationals, certificates used only at the end. Construction validity (labels, frames, schedules, phases) is reviewed separately by simulation and is not covered, except where a count required rebuilding a circuit.

Refs fetched again on 8 October: PRs 1 to 6 did not move (prs/4 was already at 8c225e6 before the fetch). A new PR 7 appeared (6725c6a, "ternary five-subset witness for conditional 373/10^11 > 2^-28", which imports PR 3 and PR 5); it is not covered. Pinned heads: prs/4 8c225e619168c0141dcfcba3b68a65bbed6a8729 (entry `4b`; 42a88ef stays pinned as `4`), prs/5 d3d370c34937503bd3fa63c83d505a05e8e50893, prs/6 5015011bd9a655da038910171eee9f431f4590ff, all on base 6e56487.

## Summary

| entry | author | claim | verdict | key recomputed numbers |
| --- | --- | --- | --- | --- |
| 4b | David Leen, head 8c225e6 | PR 3's circuit at h = 24 plus retained totals and stage sharing: R = 90950, a_c = 2970/10^11; headline unchanged at 591/10^12 | holds | base 66518 additions and 24288 outputs, 120 activated ancestors, C = 66638, q = 24312; eta = 365/1285272576; largest grid saving 2976/10^11; G_* unchanged |
| 5 | eumemic, head d3d370c (contains PR 3) | fast Gaussian resampling: Gaussian row power 2 eps + delta, eps = 49999/100000, kappa = 1479/10^12 | holds; two stale sentences in the patch text (errata) | G_* = g3 = 147947041/10^17, gap 47041/10^17; all finite constants of the new lemmas hold; several lemma steps are analytic |
| 6 | eumemic, head 5015011 (contains PR 5) | aligned bit circuit with cheaper centers: R = 494196, a = 325/10^11, kappa = 1624/10^12 | holds; the same two errata (inherited); c depends on a summation convention the note does not fix | c = 435346 rebuilt (435344 under the published conventions); eta_b = 49/1284490000; G_* = g3 = 162446751/10^17, gap 46751/10^17 |

`compare:prs`: 0 differing fields in all three new certificates (PR 4b 112 leaves, PR 5 102, PR 6 103).

The finding for the authors of PRs 5 and 6: the patches keep two sentences from PR 3 that no longer match the new parameters. In "Precision and exact recovery", `fast-gaussian-30.patch` line 263 (and `aligned-bit-30.patch` line 266) says "Proposition simultaneous-layer uses C_1 = 49961/10000, so eps C_1 < 1". With eps = 49999/100000 this gives eps C_1 = 2498000039/10^9, about 2.498, so the sentence is false as written. Derived a second way: eps C_1 < 1 needs C_1 < 1/eps = 2.00004, and 4.9961 is larger. The parameters of eq:fixed-parameters give C_1 = 19601/10000 and eps C_1 = 980030399/10^9 < 1, so the witness is not affected; 49961/10000 is PR 3's C_1 (there eps C_1 = 0.999170039). Lines 215 to 216 (218 to 219 in PR 6) give the example "d = floor(b^(19999/100000))", PR 3's exponent; eps is now 49999/100000. It is labelled "For example" and does not affect the procedure. The runner prints both as `ERRATUM` lines (observations, not in the verdict, because no step of the witness uses those values).

## Commands (from independent/ts, Bun 1.4.2)

    bun run check:prs                        # PRs 1, 2, 3, 4, 4b, 5, 6 and cross-PR observations
    bun run check:prs --only=4b,5,6          # the new entries
    bun run check:prs --only=6 --observation # also PR 6 under the published summation conventions
    bun run check:prs --only=5 --set=pr5.kappa=147947041/100000000000000000   # exit 1
    bun run compare:prs                      # seven certificates
    PR_CLONE=<clone with commits 42a88ef and 8c225e6> bun run compare:prs --only=4,4b   # proof_sha256 too

Measured on a shared 2-core container, each command on its own, under `nice`:

| command | wall time | tail |
| --- | --- | --- |
| `bun run check:prs` | 95 s | PR4b 31 checks + 43 conditions + 0 constants; PR5 26 + 41 + 20; PR6 27 + 41 + 1; all 0 failed; `VERDICT PR1 .. PR6: PASS`, then four `ERRATUM` lines; exit 0 |
| `bun run compare:prs` | 59 s | PR4b 112 leaves (61 recomputed, 30 inputs, 2 other method, 19 not compared, 0 differ); PR5 102 (41, 20 recomputed from certificate instance inputs, 36 inputs, 5 not compared, 0 differ); PR6 103 (57, 36 inputs, 2 other method, 8 not compared, 0 differ); `COMPARE PRs: no disagreement` |
| `bun run check` | 45 s | both witnesses PASS (unchanged) |
| `bun run compare` | 24 s | `COMPARE: no disagreement` (unchanged) |
| `bun test` | 263 s | `460 pass` / `0 fail` / `Ran 460 tests across 11 files` |

Rows and counts for PRs 1 to 4 are unchanged (27+35+3, 37+33+2, 47+44+3, 41+43+1). Peak memory of the largest single run (PR 6 with `--observation`) was about 560 MB.

## PR 4 at head 8c225e6 ("4b"): PR 3's shared exclusions with retained totals

Claim (`docs/research/shared-retained-complex.md`, prop:shared-retained-complex-interface of the patch): at h = 24, take PR 3's compressed side circuit unchanged (imported verbatim; `scripts/complex_circuit.py` is byte-identical to PR 3's, blob 9e83a10). Replace the central wires by retained totals E_i = sum of x_T over T avoiding i (i < h - 1) and C_* = sum of all x_T, and share stage-1/stage-3 banks. Counts: base 66518 additions and 24288 outputs; retention activates 120 ancestors and adds 24 outputs, so C = 66638, q = 24312, R = 90950. Then W = 2N + 2v^2 R = 761750114048, L = 3v^2 ((h-1)^2 + h) = 6796219584, D = 2N - 2L = 2990500480, s = 10530430586099072, eta = 365/1285272576, certifying a_c = 2970/10^11. The bit saving stays 296/10^11, so kappa stays 591/10^12: producer headroom, not a larger exponent.

Recomputed (`src/prs/pr4b.ts`, reusing `src/prs/complexCircuit.ts` with a new opt-in `retain` option): PR 3's construction rebuilt at h = 24 gives 66518 additions and 24288 outputs (12144 of each sign), side map exact. The totals are the outputs of tri over all 24 points with exclusion budget 1 on the same node store (how the PR's script forms them; the doc does not say). That gives exactly 120 newly activated additions. Every total is exact and every kept addition is disjoint. The central scatter identity holds for all 2024^2 (S, T) pairs: the coefficient is (|S cap T| - 1)/2 in both cases. Also recomputed: W, L, D, s, eta; log m < 477/50 by atanh and by Taylor; the exact slack eta - (2970/10^11)(477/50) = 406952569/627574500000000000; the Mercator enclosure of the actual saving (a* about 2.97862e-8); the gate count 3v^2(8v + 4C + 4 + 2(h-6)) = 3475338442752 < 12W; the guard with the new W, s and the unrolled recurrence; all compact conditions with sigma = 1 - 2970/10^11; G_* = g3 = 2956521/(5*10^15), unchanged because no margin depends on sigma. With PR_CLONE, all seven proof_sha256 hashes were recomputed.

Observation: the largest saving on the 10^-11 grid is 2976/10^11 (2970 is stated).

## PR 5: fast Gaussian resampling

Claim, top-down: both networks stay as in PR 3 (a = 296/10^11, a_c = 14/10^9). Only the one-dimensional resampling maps change. A chirp identity turns every Gaussian line sum into correlations evaluated by the established multiplier, with cost independent of alpha. A potential function Phi(j) = sigma(beta_j^2 + 1/4)/theta bounds the powers of E = N - I, so the Neumann series needs at most about (p+1)/(4 alpha^2) + 1/theta terms. With alpha = floor(sqrt(b/(8d))), this is at most 30d. The Gaussian cost row falls from power 3/4 + delta + 5eps/4 to 2 eps + delta, which lifts eps < 1/5 to eps < 1/2. Re-solved assembly: eps = 49999/100000, c = 9999/10000, beta = 19/25, C1 = 19601/10000, lambda = 1 - 29595/10^13, lambda' = 1 - 2959/10^12, kappa = 1479/10^12.

What changes in the parameter system, relative to PR 3 (from diffing the two cumulative patches): g5 becomes 1 - delta - 2 eps; the comparisons eps < 1/3 and 3/4 + delta + 5eps/4 < 1 are dropped and 2 eps + delta < 1 is added; the size conditions "alpha exponent < 1/2" and "gamma exponent < 1" are replaced by gamma <= b/4 and alpha^2 < p, which hold for every b and d; the new eventual conditions are b >= 96d and b >= 64 d^2. At eps = 49999/100000 the dropped conditions eps < 1/3, 3/4 + delta + 5eps/4 < 1 and the old gamma exponent condition all fail, so they must be dropped, and the patch drops them.

Recomputed (`src/prs/fastGaussian.ts`, `src/prs/pr5.ts`):

- Networks: R = 108195, W_c, s_c, eta_c from the rebuilt PR 3 circuit (unchanged).
- Parameter system: all 41 conditions; the seven margins; G_* = g3 = 147947041/10^17; G_* - kappa = 47041/10^17; eps C1 = 980030399/10^9; the guard threshold (5 + zeta - 1/eps)/4 = 0.7500149... > 3/4; "with a_c = 418/10^12 no beta satisfies both" (true at this eps and kappa: both together need a_c above about 1.18329e-8); the displayed exponents 50001/200000, 499940001/10^9, 50001/100000, 1/50000; 2^-30 < kappa < 2^-29; 1479/590 = 2.51; kappa < a/2 with kappa above 99.9% of it. Tightest stated conditions: tau < lambda, chi < lambda, lambda < lambda', each with slack 1/(2*10^12).
- Guard: the generalized guard with beta = 19/25, and the unrolled recurrence on 5005 roots.
- New Gaussian width: alpha >= 2 and alpha^2 >= b/(16d) once b >= 96d (constant 36 > 32); the Neumann chain 28d + 25/24 <= 30d at the worst case b = 96d, d = 1; 2 eta/(1 - 2 eta) = 1/(2d - 1) <= 1/4 for d >= 3; three exact instances b = 2^300000, 2^400000, 2^500000 with d = floor(b^eps) exact, where every stated bound holds. The cutoff for b >= 64 d^2 is b >= 2^(6/(1 - 2eps)) = 2^300000, so log2 n must exceed 2^300000: astronomical, but legitimate for an O-bound.
- New lemmas, finite parts (counted as constants or samples): pi by Machin's formula to 10^-30; kappa_0 = pi log2 e in (4.531, 4.534); log2 2.01 < 1.01 (201^100 < 2^101 100^100); 4.531*4 - 1.01 >= 16; 4.534/4 + 4.534/2 <= 4; 2.01 e^(-pi/2) < 0.42 (e^(pi/2) > 201/42) and pi/2 > ln 2, hence 2.01 e^(-pi x/2) < 2^-x for x >= 1; the inner-sum constants (pi > 3, 2^36 > 400); (pi/4)(1.21)/ln 2 <= 1.4, pi/(4 ln 2) < 1.14, (25 pi/4)/ln 2 <= 29; the error tallies 2^5 + 2 + 2^5 <= 2^7 and 2^7 + 2 + 2^7 <= 2^9; the precision budgets P = 3p and P = 34p for every p = 101..20000; the block windows on samples. Identities: the chirp identity (200 random rational instances) and sigma/(4 theta) + 1/4 = 1/(4 theta) + 1/2. The step identity c(j,h) - Phi(j+h) + Phi(j) = sigma h^2 + (sigma/theta) w(2y - w), its nonnegativity and X_{l,h} >= 0 were checked exactly for all j mod s and 0 < |h| <= min(3s, 120) on the certificate's five (s, t). The minimum excess is 0 in each, matching the certificate. The path bound X >= sigma sum h_i^2 - 1/(4 theta) - 1/2 held on 2000 random paths per (s, t).
- Certificate instances: the three Neumann samples (alpha, gamma, n_new, n_hvdh, n) are recomputed from the certificate's (b, d), with theta = 1/(4d).

Analytic and not checkable here (listed by the runner as observations): Harvey and van der Hoeven's Theorem 4.2 and Lemmas 2.13, 2.14 and 4.5 to 4.12, and the claims that Lemma 4.6 needs only alpha^2 theta >= 1 and Proposition 4.7(i) only ||N - I|| < 0.42; the path expansion of E^n and the passage from the lower bound on X to the operator-norm bound; the Neumann evaluation run with ||E^n|| <= 2^-p in place of ||E||^n; exactness of the packed correlation (no slot overflow) and the multiplier's cost; tape movement and the tensor cost O(d T p^(1+delta)(1 + n_*)); prime selection eta < theta_i < 1/(2d - 1) and t_i >= r/2 > p; the eventual conditions themselves; completeness of the cost table (that only the Gaussian row changes).

Errata: see the summary. Both are in the patch only; the note and the certificate use the right values.

## PR 6: aligned bit circuit with cheaper centers

Claim, top-down: only the bit network at h = 50 changes. (1) Side circuit: in every group the blocks are {2k, 2k+1} at every level, with the common point's partner a singleton kept in place. The top-level leave-one-block-out pair-star sums come from one prefix/suffix chain per pair {i, q}, shared by groups i and q, plus one group-specific triple. Each group keeps its total z_i. Counts: c = 435346 additions (totals included), q = 58800, h = 50 center roles, R = c + q + h = 494196 (was 509244). (2) Centers: each center wire carries z_i out of the side graph and loses h - 1 dimensions instead of h, so L = 3v^2 h(h-1). Then W = 2N + 2v^2 R = 394759742720000, s = Wm - N + 6v^2 h(h-1) = 49344965957616000000, Wm - s = 1882384000000, eta_b = 49/1284490000, a = 325/10^11. PR 5's assembly with tau = 1 - a, lambda = 1 - 32495/10^13, lambda' = 1 - 3249/10^12, kappa = 1624/10^12.

Recomputed (`src/prs/alignedBit.ts`, `src/prs/pr6.ts`): the generalized paired recursion (explicit root blocks, shared chains, totals) and a per-group merge with the published key rule. With the published options the generalized builder reproduces the published c = 450394 and 40256 merged additions, and the merge of `src/prs/aligned.ts` at h = 10 and 12 (tests). PR 6's circuit: c = 435346, 106294 cross-group identifications, 0 nodes pruned. Every partial output and every total is exact, every addition disjoint, every node has its common point, every node is used. Also recomputed: W, s, D, eta_b; the doc's form eta_b = (v - 6h(h-1))/(2m(v + R)) with numerator 4900 (was 4600); the previous eta_b = 23/661055000; log m < 11737/1000 by two routes; eta_b > (325/10^11)(11737/1000) with slack 1123131/513796000000000000; the Mercator enclosure (a* about 3.25044e-9); all 41 fast-assembly conditions; G_* = g3 = 162446751/10^17; gap 46751/10^17; (1 - beta) a_c = 3.36*10^-9 > 1 - lambda'; 2^-30 < kappa < 2^-29; kappa < a/2 < 2^-29; the guard (identical to PR 5's).

Gap in the text: the count depends on a summation convention the note does not fix. "The rest of the recursion is unchanged" points to the published conventions (zero terms kept in balanced sums). Under those, the same construction gives c = 435344 and R = 494194. The stated 435346 is reproduced when zero terms are dropped before the split, which is what `scripts/bit_circuit.py`'s `total()` does. That convention was identified by reading the script after the first count disagreed by 2. Both counts certify exactly 325/10^11 (326 would need R <= 492649). So the claim holds under either reading, and the stated count is reproducible only with the script's convention. The comparison "450394 to 435346" mixes the two conventions (the published circuit under the script's convention gives 450413).

Observations: the doc's "A further 3% on a_b would close this window" is right at beta = 19/25: the leaf (1 - beta) a_c > 1 - lambda' (about a) closes at a = 336/10^11, +3.4%. Moving beta down to the guard threshold 0.750015 leaves room up to about 349.97/10^11 (+7.7%). The doc's s_c < m_c^4 holds (ratio 0.456).

Not checked: the center frame argument (C_i passing D_{H_i}, H_i positive definite, complement frames in stage 2), the compiled role frames, and the schedule's scratch restoration. These are written proofs and the simulation review's domain.

## Cross-PR relations

- PR 6 contains PR 5, which contains PR 3: prs/3 (dfe5b81) is an ancestor of prs/5, and prs/5 (d3d370c) of prs/6. PR 6 leaves PR 5's notes, patch and certificate, and PR 3's construction and certificate, byte-identical. PR 5's cumulative patch keeps PR 3's `complex-circuit-31.patch` byte-identical.
- PR 4b imports PR 3's builder byte-identically and does not include PR 5 or PR 6.
- Speculation (not a claim of any PR, not in any verdict; it assumes PR 5's resampling and PR 6's bit network touch the complex producer only through m, W, s and a_c): PR 4b's network (h = 24, a_c = 2970/10^11) in PR 5's assembly at kappa = 1479/10^12, and with PR 6's bit network at kappa = 1624/10^12, passes every fast-assembly condition and the guard with its own m, W, s. kappa does not rise, because the result stays bit-limited (kappa < a/2). What PR 4b would add is room: the leaf-and-guard window for a larger bit saving widens from a < 336/10^11 (PR 3's network, beta = 19/25) to a < 712.8/10^11, and to about 742/10^11 at the guard threshold.

## Independence caveats (new entries)

- PR 4b: the doc does not say how E_i and C_* are formed. `scripts/retained_complex.py` was read to learn that they are the outputs of PR 3's `tri` over all points with budget 1. The count 120 then follows from the TypeScript rebuild of PR 3 (written from PR 3's note only).
- PR 5: written from the notes and the two cumulative patches. The certificate was opened early to learn its structure; the Python was not read.
- PR 6: the construction was written from the note. After the count came out 2 below the statement, `scripts/bit_circuit.py` was read and its zero-dropping `total()` adopted as the convention for the counted row. The published-convention count is reported as an observation.
- Certificates were opened before the code was finished, to learn their field layout; no certificate value feeds a check (PR 5's Neumann samples use only their (b, d) inputs, marked recomputed*).
- Mutation spot-check of the new code: 12 single changes were tried, and 11 are caught by the tests. The survivor removes the final prune in PR 6's merge, which removes nothing at these sizes (an equivalent mutant).

Written by Claude (Anthropic) at the direction of @fernandoeeu; not reviewed by a human.

# Addendum (8 October 2026, later): PR 7 and PR 8

Same scope and caution as above: the arithmetic only (the counts feeding each witness, derived network quantities, log enclosures, every parameter inequality, margins, the minimum and the strict comparison with kappa), exact BigInt rationals, certificates used only at the end. Construction validity (labels, frames, schedules, phases, the F3 and F2 residual arguments) is reviewed separately by simulation and is not covered, except where a count required rebuilding a circuit.

Refs fetched again: PRs 1 to 6 did not move, no PR beyond 8 exists, main is still 6e56487. Pinned heads: prs/7 6725c6a17b17871a35353fd29157f4ed851bc114 (jacklightChen), prs/8 9454645ccb61663d13dcf7cc69ade762665ae9ed (Rohan Arun), both on base 6e56487.

## Summary

| entry | claim | verdict | key recomputed numbers |
| --- | --- | --- | --- |
| 7 | F3 five-subset bit network at h = 28 (a = 3/(4*10^8)), PR 3's complex motif at h = 28 with a paired triple producer (a_c = 39/10^9), PR 5's assembly: kappa = 373/10^11 > 2^-28 | holds; one erratum inherited from PR 5's patch | global producer rebuilt at h = 28: 11240978 additions, 20475 stars, 365 templates, 3006276 replaced by 2623060, c = 10857762, R = 11840940; eta_b = 39/520019360; eta_c = 5/12693352; G_* = g3 = 934813/(25*10^13), gap 2313/(25*10^13) |
| 8 | geometric complex network on 25 points with a 26th label coordinate (m = 26^3), dyadic side circuits, a_c = 4*10^-9, the head's compact assembly with c = 1: kappa = 59/10^11 | holds (arithmetic); an unreviewed candidate | D 212737 + 2300, E 36620 + 6900, R = 258557 rebuilt from the prose alone; eta = 68/1714426753; G_* = g3 = 2956521/(5*10^15), gap 6521/(5*10^15) |

`compare:prs`: 0 differing fields (PR 7: 179 leaves; PR 8: 241 leaves in certificate.json and 162 in bit-screen.json).

## Commands (from independent/ts, Bun 1.4.2)

    bun run check:prs                        # PRs 1 to 8 and the cross-PR observations
    bun run check:prs --only=7,8             # the new entries
    bun run check:prs --only=7,8 --observation   # also PR 7's fingerprint count and PR 8's bit screen
    bun run check:prs --only=7 --set=pr7.kappa=934813/250000000000000   # exit 1
    bun run compare:prs --only=7,8
    PR_CLONE=<clone with 6e56487, 6725c6a and 9454645> bun run compare:prs --only=7,8   # source hashes too

Measured on the shared 2-core container, each command on its own, under `nice` (final runs; an earlier `check:prs` under heavier load from the other agent took 323 s and peaked at 2287 MB, before the heap was collected ahead of PR 7's build):

| command | wall time | peak RSS | tail |
| --- | --- | --- | --- |
| `bun run check:prs` | 107 s | 1885 MB | PR7 60 checks + 41 conditions + 2 constants, PR8 44 + 44 + 2, 0 failed; `VERDICT PR1 .. PR8: PASS`, then five `ERRATUM` lines (PR5 two, PR6 two, PR7 one); exit 0 |
| `bun run check:prs --only=7` | 109 s | 1574 MB | `VERDICT PR7: PASS` |
| `bun run check:prs --only=7,8 --observation` | 126 s | 2107 MB | fingerprint count 11240978 = exact-key count; bit screen winner (50, 50, 50), unique; both PASS |
| `bun run compare:prs` (no PR_CLONE) | 177 s | 1831 MB | PR7 179 leaves (108 recomputed, 39 inputs, 1 other method, 31 not compared, 0 differ); PR8 241 (118, 69 inputs, 2, 52, 0); PR8 screen 162 (97, 44 inputs, 2, 19, 0); earlier entries unchanged; `COMPARE PRs: no disagreement` |
| `PR_CLONE=... compare:prs --only=7` and `--only=8` | | | the 7 hashes of PR 7 and the 15 of PR 8 recomputed and agreeing: PR7 115 recomputed, 24 not compared; PR8 133 recomputed, 37 not compared |
| `bun run check` | 28 s | 256 MB | both witnesses PASS (unchanged); `bun run compare`: `COMPARE: no disagreement` |
| `bun test` | 191 s | 2090 MB | `512 pass` / `0 fail` / `Ran 512 tests across 13 files` |

Rows and counts for PRs 1 to 6 are unchanged.

## PR 7: F3 five-subset interchange network and paired complex producer

Claim, top-down. Commit c15ca16 imports PR 3 and PR 5 (byte-identical: the blobs of the two complex-circuit notes, the two fast-Gaussian notes, both patches, `scripts/complex_circuit.py` and both certificates equal those at prs/5). Commit 6725c6a then changes both finite networks and keeps PR 5's assembly:

1. Bit network: a new interchange motif over F3 on the five-subsets of h = 28 points, v = C(28,5) = 98280, m = h^3 = 21952, label form H = I - (2/25)J. For each common pair C (378) a local producer on the other 26 points gives the 2600 sums D_{C,E} and the retained total A_C. Scatter of the A_C minus injection of the D_{C,S\C} is the identity because C(k,2) - [k=2] = [k=5] mod 3. Identifying equal supports across the 378 producers gives 11240978 additions with q = 10v + C(h,2) = 983178 output uses; resynthesizing the 20475 four-point stars replaces 3006276 additions by 2623060, so c = 10857762 and R = 11840940. Retained outputs lose h - 2 each: L_b = 3v^2 C(h,2)(h-2). With bank sharing W_b = 2v^2(v + R), s_b = W_b m - N + 2L_b, eta_b = 39/520019360 > (3/(4*10^8))(9997/1000), log 21952 < 9997/1000.
2. Complex network: PR 3's triple motif at h = 28 with the same triple-exclusion producer (n = 28) as its disjoint producer; 61022 additions, 32816 pieces, R_c = 93838; banks shared (2v^2): W_c = 2v^2(v + R_c + h + 1), L_c = 3v^2 h(h+1), eta_c = 5/12693352 > (39/10^9)*10.
3. PR 5's fast-Gaussian assembly with eps = 4999/10000, c = 9999/10000, beta = 19/25, C1 = 19601/10000, lambda = 1 - 749/10^11, lambda' = 1 - 748/10^11, kappa = 373/10^11. The assembly hunk of the patch is PR 5's with only these numbers changed (diffed).

Recomputed (`src/prs/pairedTriple.ts`, `primeField.ts`, `pr7.ts`; reuses `complexCircuit.ts` with a new opt-in producer argument, `fastGaussian.ts`, `compact/guard.ts`):

- Local producer at n = 26: 41427 additions reachable from the 2600 outputs, by number of common points 8511 / 18616 / 14300; retaining the total adds 12 (41439). Every output exact (4604600 coefficients), the total exact, every addition disjoint, supports recomputed from the kept additions only.
- Global producer at the stated size h = 28 (exact bit-set keys: a sum whose five-sets share exactly C stays in context C; a shared 3-set is keyed with its remaining pairs, a 4-set with its remaining points): 11240978 additions (3221694 / 5013008 / 3006276 by 2 / 3 / 4 common points; 4422964 local additions identified with existing nodes), none unused, all 98280 inputs used, q = 983178. Stars: 20475 = C(28,4), 3006276 additions, 365 distinct relabelled request lists, greedy replacement 2623060 additions; every template gate was checked (operands available and disjoint, a new sum, every requested sum made). c = 10857762, R = 11840940.
- Bit network: W_b = 230640858616896000, s_b = 5063027748645128371200, D = 379712972620800, eta_b = 39/520019360; log 21952 < 9997/1000 by atanh and by e^(9997/1000) > 21952 (Taylor); exact slack 25621089/1300048400000000000; actual saving in [7.50226e-9] by the Mercator route; the retained span has rank h - 2 = 26 (rank 26 mod 1000003 on the 2600 indicators, and two linear relations cap it at 26); the matching pi is a bijection of the 98280 five-sets with |T cap pi(T)| = 2 (with an Euler circuit constructed here; the note fixes none, and any works since K13 has even degree).
- Complex network: rebuilt circuit 61022 additions (43634 disjoint, 17388 pair-star = 2(h-5)C(h,2)), 32816 pieces (9884 disjoint and 756 pair-star splits by PR 3's rule), side map exact on 7780500 coefficients, every addition disjoint; W_c = 2085111546336, eta_c = 5/12693352, slack 619909/158666900000000; actual saving about 3.94040e-8; gates 3v^2(4(61022 + 3276) + 4v + 4) = 8702721518400 < 12 W_c.
- Assembly: all 41 conditions of PR 5's system; the seven margins; G_* = g3 = 934813/(25*10^13); gap 2313/(25*10^13); C1 = 19601/10000, eps C1 = 0.97985399; displayed exponents 5001/20000, 49985001/10^8, 5001/10000, 1/5000; 2^-28 < kappa < 2^-27 (kappa is 1.00126 times 2^-28); tightest stated conditions tau < lambda, chi < lambda, lambda < lambda', each with slack 10^-11; leaf slack 47/(25*10^9). Guard with m_c = 21952, s_c = 45772350635112192 < m^5 and the unrolled recurrence (5005 roots). Gaussian width: exact instances b = 2^30000, 2^40000, 2^50000 (the b >= 64 d^2 cutoff is b >= 2^30000). Ceiling: kappa < a/2 = 3.75*10^-9 (kappa is 99.47% of it).

How much room the counts leave (observations): a = 3/(4*10^8) holds for R <= 11844078, so the stated R has 3138 roles to spare (0.027% of R). Without the star resynthesis (R = 12224156) a is not certified, so the claim rests on the exact star count. The complex side allows R_c <= 94811 (973 spare). Without bank sharing on the complex side (PR 3's 3v^2 form) eta_c would be 5/18825996 < a_c * 10, so the complex saving rests on PR 4's sharing argument applied with centers included, which is a written argument not checked here. With PR 3's a_c = 14/10^9 no beta would satisfy both the guard and the leaf at this eps and kappa (both need a_c above about 2.9837e-8).

Erratum (inherited): `prime-field28.patch` line 264 keeps PR 5's sentence "C_1 = 49961/10000, so eps C_1 < 1". With eps = 4999/10000 that gives eps C_1 = 249755039/10^8, about 2.4976, so the sentence is false as written. Second way: eps C_1 < 1 needs C_1 < 1/eps = 2.0004, and 4.9961 is larger. eq:fixed-parameters gives C_1 = 19601/10000 and eps C_1 = 0.97985399 < 1, so the witness is not affected. PR 5's other stale sentence (the example exponent 19999/100000) is corrected in PR 7 (now 4999/10000).

Not checked here: the rational frames of the F3 network (nested spans, positive definiteness from the common pair, U inside t_S^perp, the D_U and D_{U^perp} schedule and the loss count of h - 2 per retained output as an accounting of the schedule); the finite-alphabet (F3 payload) transfer and the recurrence F_k <= (s_b/W_b)F_{k-1} + O(1) over that alphabet; the bank join E inside H for both networks; the binary labels, residuals and phase interface of the complex network at h = 28; the role compilation (R = c + q is applied as an identity); the h = 8 scalar and frame simulations of the certificate; completeness of the cost table. These are written arguments or simulations.

Independence: the note's prose does not fix the local producer's summation orders or creation order (with interning they decide which decomposition is kept), nor the context order of the identification. `scripts/paired_triple_circuit.py`, `scripts/paired_exclusion_circuit.py`, `scripts/prime_field_circuit.py` and `scripts/prime_field_supports.cpp` were read before the TypeScript was written, and the construction follows them (dict insertion orders, floor split with zero terms kept, all suffix sums created, contexts in lexicographic order, the star request rule, the canonical order and the greedy tie-breaks). So the counts are a reimplementation of the PR's construction, not a reading of the prose. Written independently of the PR: the verification (supports recomputed from kept additions; brute-force five-set supports at h = 8, 10, 12 showing every root exact, every addition disjoint, one node per support and the keys' cores right; a second count of distinct supports by 128-bit additive fingerprints, equal at h = 8 to 24 and, with `--observation`, at h = 28; the independent template check), all network arithmetic, enclosures, budgets, the matching and the span rank. The PR's C++ helper was not compiled or run.

## PR 8: geometric complex-network candidate

Claim, top-down: only the complex network changes; the bit network (a = 296/10^11) and the head's compact-control assembly are kept. The complex motif keeps 25 ground points (v = 2300) but uses a 26-dimensional binary label space (one extra coordinate, charged in the arity m = 26^3 = 17576). The separate side wires become two cancellation-free circuits built by one deterministic dyadic-split rule: D (disjoint sums, 212737 additions, 2300 outputs) and E (pair-star partial sums, 36620 additions, 6900 outputs), R = 258557. No bank sharing: W = 2N + 3v^2(R + 26) = 4128046210000, L_dec = 3v^2*26*26, s = Wm - 2N + 2L_dec, eta = 68/1714426753, a_c = 4*10^-9. A new operation count gives the guard condition 32I(R + v + 26) + 4s + 4W + 4 < E_0. Assembly: eps = 1999/10000, c = 1, beta = 1/1000, zeta = 10^-4, delta = 10^-6, C1 = 49961/10000, lambda = 1 - 2959/10^12, lambda' = 1 - 2958/10^12, kappa = 59/10^11.

Recomputed (`src/prs/geometric.ts`, `src/prs/pr8.ts`, written from the note; the Python was not read): both circuits from the stated rule, which is fully deterministic (the DAG depends only on the requested family): 212737 and 36620 additions, every output's support exact, every addition disjoint, the side map (1/2)D - (1/2)E exact on all 3693800 nonzero coefficients; R = 258557; N, W, L_dec, s, eta = 68/1714426753; log 17576 in [9.77428961] by atanh and below 9775/1000 by Taylor too; eta > (4*10^-9) log m; actual saving about 4.0579e-9 (largest saving on the 10^-11 grid: 405); the audit's per-stage rank formula (R + h)m + 2va(h - 1) + 2h^2 summed over the three stages times v^2 equals Wm - 2N + 2L_dec (an identity, checked at n = 25); the operation count 8R + 38v <= 32(R + v + 26) and 32I(R + v + 26) + 4s + 4W + 4 < E_0; the guard (m >= 3, 2 <= s < m^5, E, B, C0) and the unrolled recurrence; all compact conditions with c = 1; G_* = g3 = 2956521/(5*10^15) = 5.913042e-10; gap 6521/(5*10^15) = 1.3042e-12; leaf exponent 1 - 3996/10^12; eps(1 + c) = 3998/10000; eps C1 = 99872039/10^8; 2^-31 < kappa < 2^-30; 590/83 = 7.10843; kappa above 99.6% of a/5 = 5.92e-10; tightest conditions tau < lambda, chi < lambda, lambda < lambda' at 10^-12, leaf slack 519/(5*10^11). The certificate's audit rank sums at n = 6 and 7 (12 rows) equal the stage formula with R rebuilt at those sizes.

Would it improve the head if valid: yes, by 590/83 (about 7.11 times 83/10^12). It equals PR 3's claimed kappa and is below PRs 5, 6 and 7, which use other constructions.

Observations: c = 1 is outside the range used by every earlier witness (all had c < 1), but no written condition excludes it: the layout uses max{1 - c, 0} and the stated conditions (eps c > 0, eps c < 1 - eps, eps(1 + c) < 1) hold. D and E share 6140 supports; interning across the two circuits would lower R, so the stated count is conservative. Bit screen (`--observation` and `compare:prs`): all 21 paired circuits at x = 30..70 were rebuilt with the published conventions and agree with `bit-screen.json` (additions, outputs, side roles); 441 pairs, 362 with positive deficit; (50, 50, 50) is the unique winner by the TS enclosures.

Not checked here: the geometric residual lemma over F2 (envelope labels, the unused coordinate as the norm-one vector, nonalternation of every residual, reverse frames), the phase factorization modulo 4 and the telescoping into the permitted complex operator, whether charging the extra label coordinate in the arity m = 26^3 is admissible in the layer (written argument), that the new operation count is the right count for the guard (only the inequality is checked), and that compact controls need no change. These are the PR's own review points 1 to 5 and are written arguments or simulations.

## Cross-PR relations

- PR 7 contains PR 3 and PR 5 byte-identically (commit c15ca16) and cites PR 2 (aligned pairing), PR 4 (retained totals, bank sharing) and PR 6 (cheaper centers) for ideas; it does not contain PR 4's or PR 6's code. Its local producer uses the repository's `paired_exclusion_circuit.py` unchanged.
- PR 8 is independent of PRs 1 to 7 (base 6e56487 only).
- Speculation (not a claim of any PR, not in any verdict; it assumes the assemblies take a complex network only through m, W, s and a_c): PR 8's complex network (a_c = 4*10^-9) cannot replace the complex network in PR 5's, PR 6's or PR 7's fast-Gaussian assemblies at their eps and kappa: guard and leaf together need a_c above about 1.183e-8, 1.299e-8 and 2.984e-8.

## Independence caveats (new entries)

- PR 7: the construction order was taken from the PR's scripts (see above). The certificate was opened before the code was finished, to learn its structure; no certificate value feeds a check.
- PR 8: the circuits, network, guard and assembly were written from the note only. The certificate and `bit-screen.json` were opened before the comparison code was written; `bit_screen.py` was read to learn the screen's case formula (it is also displayed in the note).
- Mutation spot-check of the new code against `test/prs/pr78-fast.test.ts`: 12 single changes (verifier flags unable to fail, the greedy tie-break reversed, the template overlap and availability checks weakened, the context order changed within a pair, the star key without its point set, the strict role budget, the matching rule, the loss h - 2, the side-map comparison and the total check). Five survived the first run; four tests were added and two strengthened, and all 12 are now caught.
- The h = 8 control counts of PR 7's certificate (1044 roles, 1156 basis inputs = roles + 2v, loss 168 = C(8,2) * 6) are compared with the TS build at h = 8; the simulations behind them are not repeated.

Written by Claude (Anthropic) at the direction of @fernandoeeu; not reviewed by a human.

# Addendum (8 October 2026, later): PRs 9 to 13

Same scope and caution as above: the arithmetic only (counts feeding each witness, rank moments, log enclosures, every parameter inequality, margins and the final strict comparison), exact BigInt rationals, certificates used only at the end. Construction validity is reviewed separately by simulation and is not covered.

Refs fetched again: PRs 1 to 7 did not move; main is still 6e56487. PR 8 moved from 9454645 to 428bb21 (one commit, "Explain geometric candidate and review scope in root README", README.md only; entry 8 stays pinned at 9454645 and its numbers are unaffected). Pinned heads: prs/9 cfd6a2baded9dba990b987934474a7721d6ca3fb, prs/10 62691e395a0458ce089a1c7b5d89e74291e95e29, prs/11 a97c1baaf354f1e370ce1e171f67453f470f66e4, prs/12 35d31e30f28bc5da0ae6a88e7b03d75ebc855534, prs/13 3ef246fa4f69c87ebfed78376418afa9ffcad145. No PR beyond 13 existed at the fetch.

## Summary

| entry | claim | verdict | key recomputed numbers |
| --- | --- | --- | --- |
| 9 | PR 7 with better star templates: R = 11670540, a_b = 761/10^11, kappa = 19/(5*10^9) = 3.8e-9 | holds | star additions 2452660 rebuilt (317 templates won by large-first, 1 by large-first descending, 47 by PR 7's rule); c = 10687362; eta_b = 117/1537792480; G_* = g3 = 4754049/(125*10^13), gap 4049/(125*10^13) |
| 10 | batched recursion on PR 7's unchanged networks: a_b = 246/10^9, a_c = 7/10^7, c = 1, eps = 7999999/16000000, kappa = 6149999/(5*10^13) > 2^-23 | holds (arithmetic); the new recurrence and basis lemmas are analytic | S_1 = 105555640096680883200; bit gap > 4.76e-11 (246 is the largest value on the 10^-9 grid); complex gap exactly 24132873235669673777179671369131/1525632551364197359955324563293421369131; path moments 553/4000, 47817969/47897500, 1213697/1260000 < 999/1000; all 29 table slacks; G_* - kappa = 362000001/(8*10^22) |
| 11 | no new exponent: dimension screen h = 24..32, explicit matching for every even h, prime-power family and obstruction bounds | holds; one cosmetic erratum (h = 28 decimal) | six screen savings reproduced to 8 digits and all below 761/10^11; matching bijective with intersection two at h = 8, 10, 24, 26, 28, 30; identity for q = 2, 3, 4, 5, 7, 8, 9, 11, 16, 25, 27; q >= 7 and q = 5 bounds below 761/10^11; q = 4 target c/Q < 4.0416 |
| 12 | PR 10's batching with a bit network at h = 30 (R = 17515487 from PR 11's screen): a_b = 253/10^9, kappa = 12649/10^11 | holds given the stated producer count (not rebuilt) | eta = 3857/52973979000; S_1 = 373570603170925665960; gap 9.413e-12 > 9e-12 (253 is the largest on the grid); 29 slacks; G_* - kappa = 4991095000007/(5*10^23) |
| 13 | auxiliary source frames on PR 10: stage-two exit of rank m - h, a third whole-residual complex class; a_b = 154/10^8, a_c = 18/10^7, kappa = 7699/10^10 > 2^-21 | holds (arithmetic); the source-frame lemma is analytic | S' = 22293445170300595200 = S_1 - B(h^2 - 2h); both stated exact gaps reproduced; third path moment 372026142559/386739360000; G_* - kappa = 492299500001/(5*10^21) |

`compare:prs`: 0 differing fields in all new certificates (PR 9 4551 leaves, PR 10 200 + 70, PR 11 206, PR 12 4796, PR 13 170; most of PR 9's and PR 12's leaves are per-template records not compared).

No recomputed number disagrees with a note. The one discrepancy is cosmetic: PR 11's README table gives the h = 28 saving as 7.6108867e-9; the formula used for the other six rows (-log(1 - eta)/log m, `explore.py`) gives 7.61088645e-9, i.e. 7.6108865. Derived a second way (mpmath, 40 digits): the stated digits equal eta/((1 - eta) log m) = 7.610886745e-9, an upper bound, so the row mixes formulas. No claim depends on it (PR 9's certified 761/10^11 is below both). The runner prints it as an `ERRATUM` line.

## Commands (from independent/ts, Bun 1.4.2)

    bun run check:prs                        # PRs 1 to 13 and the cross-PR observations
    bun run check:prs --only=10,11,12,13     # the batched entries, about 15 s
    bun run check:prs --only=9               # builds PR 7's global producer once (about 2 min, 1.8 GB)
    bun run check:prs --only=10 --set=pr10.kappa=9839998762000001/80000000000000000000000   # exit 1
    bun run compare:prs --only=9,10,11,12,13

Measured on the shared 2-core container under `nice`, each command on its own:

| command | wall time | tail |
| --- | --- | --- |
| `bun run check:prs` | 155 s | PR9 21 checks + 39 conditions + 0 constants, PR10 105 + 40 + 2, PR11 31 + 0 + 11, PR12 60 + 39 + 1, PR13 62 + 40 + 1, all 0 failed; `VERDICT PR1 .. PR13: PASS`, then six `ERRATUM` lines (PR5 two, PR6 two, PR7 one, PR11 one); exit 0 |
| `bun run compare:prs` | 172 s | `COMPARE PRs: no disagreement`; entries 1 to 8 unchanged (PR 4 without PR_CLONE) |
| `bun run check` | 26 s | both witnesses PASS (unchanged) |
| `bun test` | 181 s | `533 pass` / `0 fail` / `Ran 533 tests across 14 files` |

Rows and counts for PRs 1 to 8 are unchanged.

## What batching changes (PRs 10, 12, 13), top-down

Before: every unit of edge rank is one recursive call of width e/m, so the saving a solves s/W = m^(1-a). After: a projector edge of rank a > m/2 becomes (m - a) singleton calls and one call of width (2a - m)e/m (rational idempotent with an invertible corner, contiguous middle identity block); with the controlled basis the stage-two sink becomes two blocks (H and m - 2H); in the complex network a selected residual of rank a is one call of width a e/m. The rank sum is unchanged, so the moment at exponent 1 is still 1 - eta, but at exponent tau < 1 a wide call costs (t/m)^tau instead of t m^-tau. The new finite inequality is Psi(1 - a) = sum_i w_i r_i^(-a) < 1 with rank-mass weights w_i = copies_i t_i/(W m) and widths r_i = t_i/m, certified by e^x <= 1/(1-x) and rational log upper bounds. Recomputed here: every class rank, width and copy count, S, the weights, the log bounds (as upper bounds of this checker's own atanh enclosures), the bound, its exact gap, and a second route with a sharper exponential bound and the checker's own logs. Room: the stated a_b is the largest value on its grid in PRs 10, 12 and 13 (the next grid value fails even the true moment's lower bound); the complex savings have room (PR 10: 72/10^8 against 70; PR 13: 181/10^8 against 180).

The guard changes too: one dependency path meets at most one selected class (every selected rank exceeds q/2 for q = m + 6h = 22120), and the depth recursion with rho = 6/5 needs three (PR 13: four) path moments below 999/1000; then C_1 = 6/5 - beta/5 + zeta = 11999/10000, so eps C_1 < 1 allows eps near 1/2. Recomputed: 160000^5 < m^6, each Taylor value, and (independently) that each Taylor value bounds (a/m)^(6/5) from above by an exact fifth-power comparison; 36W^3 + 4s + 4W + 8m + 4 < E; E, C_dep and C_0 (equal to the certificates').

Analytic, not finite arithmetic (printed as observations, never counted): the arbitrary-width recurrence lemma (Psi(tau) < 1 gives O(e^tau) with floors, remainders and row padding); the pivot profile of idempotents; existence of one rational basis meeting all corner conditions (a nonvanishing-polynomial argument, not materialized at h = 28 or 30) and of the controlled basis; that the classes are what the producer's frames give; the whole-residual identity C^{-1} = -iZCZ with mixed signs; the dependency-path budget q = m + 6h and the depth induction; the mixed-width complex layer bound and the compact-control interface at c = 1; the chirp precision correction (only its integer budget p + 29p + ceil(log2(2^B L_A)) + 11 <= 34p is checked, for every p = 101..3000 and every alpha); the compact sorting cost; completeness of the cost table. PR 13 adds the source-frame lemma (Phi_{I+M} Phi_{-M} = Phi_I, gates and interior edges unchanged) and the common basis for the new exit class. PR 12 adds that the controlled basis and frame schedule carry over to h = 30 and that a bit network at h = 30 combines with a complex network at h = 28.

## PR 9: refined star templates

Claim: PR 7's network, but each of PR 7's 365 canonical star templates is re-synthesized by three rules (PR 7's greedy; on equal pair frequency prefer the larger union, then ascending union mask; the same with descending masks), unused gates are pruned and the smallest circuit per template kept. Recomputed (`src/prs/starRules.ts`, `pr9.ts`, on entry 7's rebuilt global producer): 2452660 star additions (saves 170400 over PR 7), every candidate gate valid; c = 10687362, R = 11670540; eta_b = 117/1537792480 > (761/10^11)(9997/1000), also by the Mercator route; PR 5's 41 conditions and 7 margins at the new numbers; G_* = 3.8032392e-9; kappa > 2^-28; 380/373 - 1 = 1.877%; the guard with PR 7's complex network. Room: R may grow by 915 roles (0.008%) before 761/10^11 fails, so the claim rests on the exact template count. With only the large-first rule the total is already 2452660.

## PR 10: batched recursive networks

Numbers as in the summary and the top-down section. Also recomputed: the intermediate three-class moment (a_b = 177/10^9, gap > 1.78e-10; 177 is also the grid maximum); the data rank identity 2N sum_j (d_j + h - 1) + N = 2Nm - N; S_0 - S_1 = B h^2; R_c = 93838 rebuilt (PR 7's complex circuit); B_c, W_c, L_c, s_c, S_c; the 29 slacks one by one against the patch table; the seven margins; leaf exponent 1 - 6993/10^10; eps C_1 = 95991988001/(16*10^10); exponents (1 - eps)/2, eps c, 1 - eps, 1 - 2 eps; 2^-23 < kappa < 2^-22; kappa = 0.9999998 a_b/2. Without batching the same network certifies only about 7.502e-9; batching multiplies the bit saving by about 32.8. Note: b >= 64 d^2 needs b >= 2^48000000 at this eps (legitimate for an O-bound, astronomically late). The g4 row (CRT and axis layouts with d instead of d^2) is the same margin (1 - eps)(1 - tau) as in the compact-control system already used by entries 5 to 9.

## PR 11: dimension screen, matching, prime-power family

Recomputed (`src/prs/pr11.ts`): the six new rows of the table from the stated R (PR 7's interface at each h) to the stated 8 digits, each rejected against 761/10^11 by an upper enclosure; the README's insertion rule gives a cyclic edge order of K_k (k = 3..15) with consecutive edges sharing one vertex, and the resulting matching is a bijection with |T cap pi(T)| = 2 on all C(h,5) five-sets at h = 8, 10, 24, 26, 28, 30 (PR 7's Euler construction needs 4 | h); the identity C(j, q-1) - [j = q-1] = [j = 2q-1] mod p for eleven prime powers (and its failure for q = 6); h = r^2/t integral only at q = 2 for q <= 2000; C(h,t)C(h-t,q) = C(h,r)C(r,t); the q >= 7 bound eta <= 1/(2*20^3*1717) gives a <= 4.0503e-9 < 761/10^11; q = 5: negative deficit at h = 14, bounds below 761/10^11 for h = 15..29 and at h = 30 for the decreasing tail; q = 4 at h = 27 needs c/Q < 4.0416 (README: "roughly fewer than 4.04"). Not rebuilt: the producer counts at h != 28.

## PR 12: dimension 30 with controlled batching

Recomputed from proof.tex: v, m, Q = C(28,3)C(30,2) + C(30,2) = 1425495, R = c + Q, eta, ranks 26940, 26100, 26071, singletons 60, 0, 929, blocks 26880; 25200 and 900; 25142, S_1, the moment with the checker's own log bounds rounded up to 10^-9 (gap 9.413e-12 > 9e-12) and by the second route; the 29 slacks against the patch table; margins; G_* - kappa = 9.98219e-12; kappa > 2^-23; 2.837% above PR 10 (README: 2.84%). The complex network and guard are PR 10's (entry 10). Room: R may grow by 2332 roles (0.013%) before 253/10^9 fails, so the result rests on the h = 30 producer count c = 16089992, which this run does not rebuild (the h = 28 build already needs about 1.8 GB). What is missing for a full check: an h = 30 rebuild of the global producer with PR 9's star rules.

## PR 13: auxiliary source frames

Recomputed: exit rank m - h = 21924 (28 singletons, block 21896); rank per stage-two role still m (756 + 28 + 21168 = 0 + 28 + 21924); S' by the rank sum and as S_1 - B(h^2 - 2h); widths, weights, both exact gaps as stated; the third complex class (d_3 = 21141, 2v_c^3 = 70317217152 copies), S_c' = 903222851311872; the third path moment and 2 d_3 > q; assembly, margins, 2^-21 < kappa < 2^-20; kappa = 6.2593 times PR 10's. Certificate fields agree, including `improvement_over_PR10` = 38495000/6149999.

## Cross-PR relations

- PR 10 imports PR 7 (and through it PR 3 and PR 5) byte-identically: scripts, notes and the three certificates have PR 7's blobs.
- PR 11 contains PR 9 (commit cfd6a2b is its first commit). PR 12 and PR 13 each contain PR 10's commit 62691e3; PR 12 also carries PR 9's and PR 11's research directories byte-identically.
- PR 12's h = 30 producer (R = 17515487) is the h = 30 row of PR 11's screen, and the h = 28 row of that screen is PR 9's R.
- Speculation (not a claim of any PR, not in any verdict; it assumes the source-frame change and the h = 30 network are independent and that PR 13's lemma carries over to h = 30): PR 13's source frames applied to PR 12's h = 30 network, and PR 9's smaller R = 11670540 under PR 10's or PR 13's batching, are untested combinations. With R = 11670540 the PR 13 moment would only change through S and the weights; it was not evaluated here.

## Independence caveats (new entries)

- PR 9: the tie order and candidate set were read from `star_duality.py` and `verify.py` (the README does not fix them); the count is a reimplementation of that rule on this checker's own build of PR 7's producer.
- PRs 10, 12, 13: written from the notes and patch hunks; the Python was not read. PR 10's certificate was opened before the code was finished (its head, including the guard constants, was printed to learn its structure); no certificate value feeds a check.
- PR 11: written from the README. `explore.py` was grepped for its saving formula only after the h = 28 digits disagreed.
- Failure-mode tests (`test/prs/pr913-fast.test.ts`, 21 tests): a_b one grid step up fails both routes; an understated log bound and a too-small Taylor value are rejected; R + 20000 (PR 10) and R + 2400 (PR 12) fail; S' + 1 and a_b = 155/10^8 fail PR 13; kappa = G_* fails PR 10; eps = 1/2 makes a table slack non-positive; star-rule candidates are checked gate by gate; a broken matching rule and q = 6 are rejected.

Written by Claude (Anthropic) at the direction of @fernandoeeu; not reviewed by a human.

# Addendum (8 October 2026, later): PRs 14 to 16

Same scope and caution as above: the arithmetic only (role and rank counts that feed each moment, child lists, log enclosures, moments, path guards, every parameter inequality, the margins and the final strict comparison), exact BigInt rationals, certificates used only at the end. Construction validity (labels, frames, schedules, the new basis lemmas) is not covered.

Refs fetched again: PRs 1 to 13 did not move (prs/8 is still at 428bb21, as recorded); main is still 6e56487; no PR beyond 16 exists. Pinned heads: prs/14 1fa5b9a9aaccbebb3eb29ac7ea55811f46464eee (Rohan Arun), prs/15 a17cab396ce1c79c288bde9d06002cefdc0af8e6 (eumemic), prs/16 a80f5e676c84b59def9791495df0655efe89a04f (jacklightChen).

## Summary

| entry | claim | verdict | key recomputed numbers |
| --- | --- | --- | --- |
| 14 | PR 12's h = 30 producer + PR 13's source frames + two new data-corner blocks (842, 782): a_b = 1816/10^9; PR 13's complex classes with a_c = 18179/10^10; kappa = 90799/10^11 | holds (arithmetic), given PR 12's producer count (not rebuilt) | S = 65379670780393117512 (two derivations); bit gap 1.915420e-10 > 1.9154e-10; complex gap 2.11963e-11; leaf (1 - beta) a_c = 18160821/10^13; G_* - kappa = 40919500001/(5*10^21) |
| 14-E | held-back controlled-corners candidate: a_b = 40315/10^11, kappa = 5039/(25*10^9) with PR 10's complex network | holds (arithmetic); superseded inside the PR | same S; gap 1.4208e-12; G_* - kappa = 14957569250021/10^24 |
| 15 | smaller h = 30 producer (R = 13056812) + source frames; every complex residual batched (a_c = 4191487/10^12), rho = 3/2 guard; kappa = 1076678/10^12 > 2^-20 | holds (arithmetic), given the producer count and the complex rank histogram, neither rebuilt; the histogram appears only in the certificate | eta = 3857/39597954000; S = 58481015896548325080; bit gap 9.4e-15 (own logs), complex gap 1.56e-14; path bound 0.9972067 < 27921787004127/(28*10^12); eps = 49999946161/10^11 from the stated rule; G_* - kappa = 170276524048839/(5*10^26) |
| 16 | h = 32 producer (R = 25224960) + source frames + data corners + nested basis (diagonal exit corner, one block of h); every complex residual batched (a_c = 4/10^6); kappa = 9799/10^10 > 2^-20 | holds (arithmetic), given the h = 32 producer count (not rebuilt) | W, L, s, eta = 3503/52073136128 and (N - 2L)/N = 113/203 as stated; S = 167747380096422805504; bit gap 3.081e-10 > 3e-10; complex histogram rebuilt from the note, rank sum = s; complex gap 1.835e-8; Taylor path bound exactly 11005895/11035584; G_* - kappa = 490199500001/(5*10^21) |

`compare:prs`: 0 differing fields in all four new certificates (PR 14 source-frame-corners 2077 leaves, controlled-corners 5882, PR 15 812, PR 16 6481; most leaves are matrix controls, producer audit records and hashes, not compared).

No recomputed number disagrees with any note, README or certificate. Nothing had to be reduced or re-derived because of a disagreement.

What the verdicts rest on (the points an author or reviewer should know):

- PR 15 has almost no role slack. With its own child list, a_b = 2153359/10^12 survives up to R = 13056973, so the stated R = 13056812 leaves 161 roles (0.0012% of R). The claim stands or falls with the exact count of the new h = 30 producer (14381873 additions, 142941 outputs, 1468002 delivery roles removed by bilateral reuse), which this checker cannot rebuild (the h = 30 producer already exceeded the memory budget for PR 12). The certified gaps are also tiny: 9.4e-15 for the bit moment with this checker's own logs (7.7e-15 with logs rounded up to 10^-9), 1.56e-14 for the complex moment. Both are exact and positive.
- PR 14 rests on PR 12's count (R = 17515487; 50033 roles of slack, 0.29%). PR 16 rests on its own h = 32 count (R = 25224960; 126346 roles of slack, 0.50%).
- PR 15's complex rank histogram (33 nonzero ranks, global copies) is not in any of its documents; it is used here as an input from the certificate and checked for consistency (rank sum equals s, bulk multiplicities B_c, B_c, 2v^3, all ranks proper). The doc's "the executable schedule counts 34 residual ranks" matches the certificate only if rank 0 is counted (cosmetic).

## Commands (from independent/ts, Bun 1.4.2)

    bun run check:prs                        # PRs 1 to 16 and the cross-PR observations
    bun run check:prs --only=14,15,16        # the new entries and X3, about 30 s
    bun run check:prs --only=15 --set=pr15.kappa=538339170276524048839/500000000000000000000000000   # exit 1
    bun run compare:prs --only=14,15,16
    bun test test/prs/pr1416-fast.test.ts    # 16 failure-mode tests, about 25 s

Measured on the shared 2-core container under `nice`, each command on its own:

| command | wall time | peak RSS | tail |
| --- | --- | --- | --- |
| `bun run check:prs` | 139 s | 1940 MB | PR14 58 checks + 77 conditions + 1 constant, PR15 38 + 40 + 1, PR16 55 + 40 + 1, all 0 failed; `VERDICT PR1 .. PR16: PASS`, then the six known `ERRATUM` lines (PR5 two, PR6 two, PR7 one, PR11 one); exit 0 |
| `bun run compare:prs` | 200 s | 1829 MB | `COMPARE PRs: no disagreement`; entries 1 to 13 unchanged |
| `bun run check` | 28 s | 252 MB | both witnesses PASS (unchanged) |
| `bun run compare` | 15 s | 208 MB | `COMPARE: no disagreement` (unchanged) |
| `bun test` | 234 s | 1948 MB | `549 pass` / `0 fail` / `Ran 549 tests across 15 files` |

Rows and counts for PRs 1 to 13 are unchanged. One shared helper changed: `batchedAssemblyRows` in `src/prs/pr10.ts` takes an optional `rho` (default 6/5, so earlier entries are untouched) for the C1 identity row.

## What PRs 14 to 16 change, top-down

All three keep PR 10's mixed-width recurrence and PR 13's source-frame move and change only the child list, i.e. which rank units of which edges are compiled as one wide child. The rank sum s, the deficit and eta are those of the unchanged scalar network, so the weights still sum to 1 - eta; only the widths move. The moment Psi(1 - a) = sum w_i r_i^(-a) < 1 is the finite claim; the lemmas that justify each block (pivot profiles inside corners, one rational basis for all conditions) are analytic.

- Data corners (PR 14 and PR 16, found independently by their account): the stage-two data entrance (2N copies, rank (h-1)^2) gets 2h - 1 singletons and a block H - 4h + 2; the stage-three data entrance (rank (H-1)(h-1)) gets 3(h-1) singletons and blocks H - 2(h-1) and m - 2(H + h - 1). At h = 30 these are 782 and 842 + 25142; at h = 32, 898 and 962 + 30658.
- Nested basis (PR 16 only): restricting the controlled basis one more level makes the source-frame exit's h-corner diagonal, so its h singleton pivots become one block of width h. At h = 32 this is what lifts a_b from about 1.899e-6 (largest on the 10^-9 grid without it) to 1.96e-6 > 2^-19.
- All complex residuals (PR 15 and PR 16, independently): every nonzero edge of PR 7's h = 28 complex network is one child of width equal to its rank. The guard then needs a path moment for arbitrary child lists: total rank at most q = m + 6h, parts at most M = m - 2h, so by convexity at rho = 3/2 the moment is at most (M/m)^(3/2) + ((q - M)/m)^(3/2) < 999/1000, and C1 = 3/2 - beta/2 + zeta = 3749/2500.

## PR 14: source frames with h = 30 data corners

Provenance: one commit on PR 12's head 35d31e3 (so it contains PRs 12, 10, 7, 9, 11 byte-identically). Modified files: Makefile, NOTICE, README.md; everything else is added. The pinned copy under `research/source-frame-corners/pr13/` (three notes, certificate, two scripts, test) has exactly the blobs of prs/13 (2273bc5, 0f36448, 839714c, ccc6375, 113c1ae, 2e016e0, d775a50). New: `research/controlled-corners/` (held-back candidate, proof.tex), `research/source-frame-corners/` (proof.tex, complex.tex, certificate, matrix checks), two patches, a PDF.

Recomputed (`src/prs/pr14.ts`): ranks, singleton counts and widths of the four classes from h (each class sums to its rank); S by the class sum and as PR 12's S_1 - 840 B - 2N(842 + 782) (the controlled-corners S_2 is the same number because 25200 + 900 + 840 = 26940); weights sum to 1 - 3857/52973979000; the moment with own logs rounded up to 10^-10 (gap 1.915420e-10 > 1.9154e-10) and by the second route; negative controls named by the README (dropping either data block fails at 1816/10^9 already by e^x >= 1 + x). Complex: PR 13's classes and displayed logs unchanged, gap at 18179/10^10 = 2.11963e-11 > 2.1196e-11; leaf (1 - beta) a_c = 18160821/10^13 > 1816/10^9 (slack 8.21e-11). PR 13's guard rows (three classes, rho = 6/5). Assembly: all conditions, seven margins, G_* = g3, gap as stated, gap > 8.1839e-12 (slack 2*10^-22), 17.936% above PR 13; 2^-21 < kappa < 2^-20. Section 14-E: the controlled-corners candidate (seven blocks incl. 25200, 900, 840) at 40315/10^11 (gap 1.4208e-12 > 1.4e-12), its assembly with PR 10's complex saving, 59.35% above PR 12.

Room: a_b up to 1820/10^9 on the 10^-9 grid; complex up to 18180/10^10 (18179 with PR 13's displayed logs); 40315 is already the grid maximum for 14-E.

Not checkable by arithmetic here: the corner lemmas (Pi_t tensor Pi_U with a nonsingular b-corner; I - Z with rank Z <= r and its Schur complement; the color-block witnesses), one rational basis for all exit, join and data conditions at h = 30, the physical pivot order, PR 13's lemma at h = 30 and the absence of double counting; the h = 3, 4, 5 matrix controls in the certificate were not re-run; PR 12's producer.

## PR 15: smaller h = 30 network with every complex residual batched

Provenance: one commit on PR 6's head 5015011 (so it contains PRs 3, 5, 6, not PR 7 or PR 10 as commits). It adds PR 7's network files at PR 7's blobs (`scripts/paired_triple_circuit.py` 6b10e49, `prime_field_circuit.py` e469111, `certificates/prime-field28.json` 0c50595, `notes/prime-field28-construction.tex` 21ce20f, `patches/prime-field28.patch` 764026f and the rest), and pinned copies `references/pr10`, `references/pr12`, `references/pr13` whose files all have the blobs of prs/10, prs/12, prs/13 (only the added SOURCE.json manifests are new). Modified: Makefile, NOTICE, README.md, docs/reproducibility.md, docs/research/current-status.md. The headline is `docs/research/source-frame-stream.md` with `scripts/source_frame_stream_network.py` and the certificate; much else is labelled experiment.

Recomputed (`src/prs/pr15.ts`): the producer arithmetic as stated (14381873 + 142941 = 14524814; minus 1468002 = 13056812; outputs v + C(30,2); center loss C(30,2) * 28 = 12180); W, eta = 3857/39597954000, S; the three source-frame classes; the moment with own logs, with logs rounded to 10^-9 and by the second route. "The next grid point fails the conservative bound" is reproduced (2153359 is the largest 10^-12 value with 1/(1 - x), both with own and with 10^-9-rounded logs; the sharper second route would allow 2153380). Complex: s of PR 7's network; the histogram's rank sum equals s; its rank-1 class equals the remaining singleton count; bulk multiplicities; all 33 ranks in [1, m), maximum 21896; moment at 4191487/10^12 with own logs (gap 1.56e-14 > 1.34e-14) and by the second route; the certificate's next-grid moment recomputed from its own logs. Guard: q = 22120; M < q < 2M; (M/m)^(3/2) + ((q - M)/m)^(3/2) <= 0.99720668 (exact upper square roots on a 10^-20 grid) < 27921787004127/(28*10^12) < 999/1000; 36W^3 + 4s + 4W + 8m + 4 < E; at most s nonzero edges; C1 = 3749/2500; E, C_dep, C0 equal to the certificate's. Assembly: eps from the stated rule (1 - delta)/(2 + a_b) rounded down to 10^-12 gives 49999946161/10^11 (equal to the certificate); all conditions; G_* and the gap as stated; kappa > 2^-20; 538339/812 = 662.979; 39.85% above PR 13; 18.58% above PR 14 ("18.6%").

Observation (fitted here, not stated by the PR): the per-invocation physical rank sums 399994068 (h = 30) and 250925864 (h = 28, R = 8771396 in batched-stream.md) both equal (v + R)h + (h - 2)v + 2 C(h,2)(h - 2).

Not checkable here: the producer (ZDD support audit, star rewriting, the physical register allocator and bilateral reuse), the 142506-image matching, the frame audit and the 60-node delayed source cut; that reused registers keep every auxiliary's boundary frames so PR 13's lemma and the controlled basis apply; that the histogram is the complete physical-edge list and every residual has an orthonormal basis; the path budget and convexity relaxation; PR 10's inherited lemmas.

## PR 16: nested source-frame batching at h = 32

Provenance: parent 1051e25 merges prs/13 (3ef246f) into main; a80f5e6 adds `research/nested-source/`, `notes/nested-bit.tex`, `notes/nested-complex.tex`, `patches/nested-source.patch`, a PDF, and PR 12's `research/prime-field-followup/` and `research/geometric-dimensions/` at PR 12's blobs (18 files, all identical). Modified: CITATION.cff, Makefile, NOTICE, PATCHING.md, README.md, SOURCES.json, docs/research/current-status.md. It shares no blob with PR 14's or PR 15's added files except copies of PR 12 and PR 13 files, consistent with its statement that it imports neither.

Recomputed (`src/prs/pr16.ts`): v, m, Q_out = C(30,3) C(32,2) + C(32,2) = 2014256, R = c + Q_out, C(32,4) = 35960 stars; W, L, s, eta and (N - 2L)/N = 113/203 exactly as stated; B; the four classes from h (ranks, singletons, blocks; the stage-three profile sums to (h - 1)(H - 1)); S = 167747380096422805504; the moment with own logs below 1 - 3*10^-10 (gap 3.081e-10); second route; a_b > 2^-19; without the nested corner the moment fails at 1960/10^9 (largest then 1899/10^9). Complex: B, W, D, s; the local table sums to 2806804 = (2v + R + h + 1)h - 2v + 2h(h + 1); the global histogram (3v^2 c_r plus five classes) has rank sum s and all ranks in [1, 21896]; the moment at 4/10^6 (gap 1.835e-8 > 1.83e-8) and at 419/10^8; second route. Guard: t = 1/392, y = 1/98; the Taylor bound (1 - t)^(3/2) <= 1 - 3t/2 + (3/8)t^2/(1 - t) checked exactly by squaring; y^(3/2) < y/9; the sum is exactly 11005895/11035584 < 0.99731 < 999/1000; constants and C1 = 3749/2500. Assembly: all conditions, minimum margin and gap as stated, kappa > 2^-20, 27.28% above PR 13, 7.92% above PR 14, 2.75% above 2^-20.

Room: a_b up to 1969/10^9 on the 10^-9 grid; a_c up to 419/10^8.

Not checkable here: lem:nested-source-basis (one rational K_0, J_beta, G_i meeting all A1, A3, A4 and data-entrance conditions with the diagonal A4 corner, both orientations), the data-entrance and A3 corner lemmas, lem:nested-source-interchange; the h = 32 producer (561 templates, support rebuild), source-span nondegeneracy and the matching at h = 32; that the complex histogram is the complete edge list and the residual bases; the finite matrix and dirty-scratch controls; PR 10's inherited lemmas.

## Cross-PR relations

- Ancestry: PR 14 contains PR 12 (and so PR 10, 7, 9, 11); PR 15 contains PR 6 (and so 5, 3) and carries byte-identical copies of the PR 7, 10, 12 and 13 files it uses; PR 16 contains PR 13 (and so PR 10, 7) and PR 12's research directories. None of 14, 15, 16 contains another.
- PR 15 and PR 16 build the complex rank histogram of the same network by different schedules and disagree on its shape, not its sum: PR 15 has N = v^3 = 35158608576 fewer rank-756 edges (stage-two auxiliary entrances, B_c in PR 16) and N more edges of each of ranks 27 and 729 (27 + 729 = 756). Both sum to s. Each PR's a_c also holds on the other's histogram (second route). Which is the actual edge list is a construction question not settled by arithmetic.
- Speculation (not a claim of any PR, not in any verdict; it assumes the corner and nested-basis lemmas apply unchanged to PR 15's reused registers): PR 15's producer with PR 14's two data blocks would certify about a_b = 2.3826e-6, and with PR 16's nested exit corner as well about 2.4967e-6 (second route, 10^-12 grid), against PR 15's 2.1534e-6. Since every entry here is bit-limited (kappa about a_b/2), that would suggest kappa near 1.25e-6 if the complex side and the assembly carried over; this was not assembled or checked.

## Independence caveats (new entries)

- PR 14 and PR 16: written from the proof notes and READMEs; the Python was not read. Log bounds are this checker's own atanh enclosures (rounded up to 10^-10 for PR 14 as its proof describes, unrounded for PR 16).
- PR 15: written from the docs; the Python was not read. The complex rank histogram is an input copied from the certificate (no document states it); the checks on it are consistency checks, not a rebuild. The rank-sum formula in the observation was fitted to the two stated numbers.
- All three: certificates were opened before the code was finished to learn their structure (field names, the order of the moment items); no certificate value other than PR 15's histogram feeds a check. The producer counts at h = 30 and h = 32 are inputs.
- Failure-mode tests (`test/prs/pr1416-fast.test.ts`, 16 tests): a_b one grid step past the maximum fails (PRs 14, 15, 16); R + 50034 (PR 14) and R + 162 (PR 15) fail; a misstated S, gap claim or minimum margin fails; kappa = G_* fails; a complex saving below the leaf limit (PR 14) or past the moment (PR 16, 5/10^6) fails; a tampered histogram (PR 15) or local table entry (PR 16) breaks the rank sums; an understated path bound and an off-grid epsilon fail; rho = 6/5's C1 is rejected at rho = 3/2; the nested corner is necessary at 1960/10^9. No mutation run was done for the new code in this session.

Written by Claude (Anthropic) at the direction of @fernandoeeu; not reviewed by a human.
