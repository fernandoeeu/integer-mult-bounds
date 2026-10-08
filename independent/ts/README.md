# Independent TypeScript checker for the conditional witnesses

This directory is a second implementation, in TypeScript on Bun, of the finite
arithmetic behind the repository's conditional bounds
`T(n) = O(n (log n)^(1 - kappa))`:

- the **current** compact-control witness `kappa = 83/10^12 > 2^-34`
  (`notes/compact-control-*.tex`, `notes/independent-complex.tex`,
  `patches/compact-control-34.patch`, review guide
  `docs/research/compact-control-review.md`);
- the **preserved** earlier witness `kappa = 2^-59`
  (`notes/paired-*.tex`, `notes/stopped-guard.tex`, `patches/h50-paired-59.patch`).

Both witnesses use the paired bit network at `h = 50` with bit saving
`a_b = 296/10^11`. This checker rebuilds that circuit and verifies it, and it
recomputes the numbers each witness uses. It works from the written notes and
patches, in exact rational arithmetic, separately from the Python scripts.
Its value is as a cross-check: an error in one implementation, or a number in
a note that the mathematics does not support, should show up as a
disagreement.

**Caution.** Passing these checks means that the finite arithmetic and the
finite circuit facts listed below hold. It is **not** a formal verification of
the multiplication theorem, and it is not a review of the written proofs. Both
results remain conditional on OpenAI's manuscript *Integer multiplication
below n log n* (pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`), whose
theorem this repository assumes without verifying. They are also conditional on
the repository's written extensions, which have not been independently reviewed.
For the current result these are the compact-control movement, layout, guard
and independent-complex arguments.

## Running it

Requires Bun (tested with 1.4.2). There are no dependencies and no build step.

```sh
cd independent/ts
bun run check      # every row for both witnesses, then one verdict per witness; exit code 0 iff all hold
bun test           # 339 tests: identities, failure modes, and completeness of the failure tests
bun run compare    # field-by-field comparison with the two JSON certificates
```

Options for `bun run check`:

- `--verbose` prints the source statement next to every row.
- `--only=59` or `--only=compact` selects one witness. The shared bit network
  always runs.
- `--no-observation` skips the second circuit build, which serves only the
  conventions observation below and is not part of either verdict.
- `--set=<59|compact>.<parameter>=<p/q>` replaces one stated parameter, so you
  can watch the rows reject it. Derived parameters are **not** recomputed. For
  example, `compact.beta` leaves `C1` as stated, and the guard rows then
  reject it.

Measured on one Linux container (2 cores, Bun 1.4.2, with `BUN_OPTIONS=--smol`
set by that environment), each command run on its own:

| command | wall time | tail of output |
| --- | --- | --- |
| `bun run check` | 22.2 s | `VERDICT 2^-59 witness (preserved): PASS ...` / `VERDICT compact-control witness (current): PASS ...` |
| `bun test` | 37.5 s | `339 pass` / `0 fail` / `Ran 339 tests across 7 files.` |
| `bun run compare` | 10.7 s | `COMPARE: no disagreement` |

`check` builds and verifies the `h = 50` circuit twice, once per summation
convention (about 10 s each). `--no-observation` brings it to about 13 s.

A parameter moved past its limit makes the run fail with exit code 1. For example:

```
$ bun run check --only=59 --set=59.epsilon=198/1000
VERDICT 2^-59 witness (preserved): FAIL ...
FAILED: [2^-59 witness (preserved)] kappa < G = min g_j: slack -35679856197903889/21474836480000000000000000000000000000
FAILED: [2^-59 witness (preserved)] G = min g_j: got 135395469/78125000000000000000000000, note says 272158569/156250000000000000000000000
...
$ bun run check --only=compact --set=compact.epsilon=1988/10000
VERDICT compact-control witness (current): FAIL ...
FAILED: [compact-control witness (current)] G_* = 333833/(4*10^15): got 82999/1000000000000000, note says 333833/4000000000000000
FAILED: [compact-control witness (current)] kappa < g3: slack -1/1000000000000000
...
```

## The current witness, top-down

```
paired-block circuit, n = 49 points per common point                      B1  rebuilt from the prose, every coefficient verified
  -> merged over the 50 common points: c = 450394 additions,             B1  recomputed; merge verified group by group
     q = 58800 partial outputs, R = c + q = 509194 side roles                 (R = c + q is the note's identity)
    -> bit network at h_b = 50: W_b, s_b, eta_b = 23/661055000            B2  recomputed from the note's formulas
      -> log m < 11737/1000 and eta_b > a_b * 11737/1000                  B2  two independent enclosures of log m
        -> bit (swap) exponent tau = 1 - a_b, a_b = 296/10^11
original complex network at h_c = 25 (construction not rebuilt)            C1  counts recomputed from the formulas
  -> eta_c = 14/3464399375, log m_c < 966/100,                            C1  two enclosures of log m_c
     eta_c > a_c * 966/100, a_c = 418/10^12, sigma = 1 - a_c              C6  third route: enclosure of the actual saving
generalized guard: E, B, C0, C1 = 5 - 4 beta + zeta                        C4  constants, comparisons, unrolled recurrence
layer exponents chi, chi_leaf, chi_reserve against lambda < lambda' < 1    C3  stated parameter conditions
Gaussian width alpha = ceil((32 d b)^(1/4)), gamma = 2 d alpha^2           C5  exponents, cutoff, five concrete instances
seven margins g1..g7  ->  G_* = min g_j = g3 = 333833/(4*10^15)            C3  recomputed and compared with the note
  -> kappa = 83/10^12 < G_*, gap 1833/(4*10^15), 2^-34 < kappa < 2^-33    C3
scoped ceiling: kappa < a*/5 <= 8.369598075e-11 < 2^-33 for this motif    C6
```

What the chain does **not** contain, and this checker cannot supply, is the
algorithm: that the multitape machine performs the compact-control movement,
the layout and the repair at the costs the notes claim. Those are proofs in
the notes. The checker's part is the numbers those proofs consume. See
[Obligations outside any arithmetic checker](#the-review-guides-new-obligations).

## How rows are classified and counted

Every comparison is exact, on `BigInt` rationals (`src/rational.ts`). Floating
point never enters a decision. Decimals are printed only for reading.
Every printed row has a kind:

| tag | kind | meaning | counted? |
| --- | --- | --- | --- |
| `ok` | recomputed check | involves a value this checker recomputes (circuit facts, counts, rank deficits, enclosures, guard constants, displayed exponents and margins, sampled instances), compared with what the note states | yes |
| `ok p` | parameter condition | a comparison the note states between its own input parameters (for example `tau < lambda`). Nothing is recomputed. It fails when a parameter moves past the stated limit | yes, separately |
| `ok c` | constant | a comparison between numbers written inside a note's argument, independent of the witness (for example `36 < 128`). It fails only if the note's constant is wrong | yes, separately |
| `ok s` | lemma sample | finite instances of a general claim of a note that does not depend on the witness (the repair density bound for `p = 2..4096`, the four-update identity on a box) | yes, separately |
| `id` | identity | true for every admissible input, for example `s(8+E) <= 9B^2` with `B = s + E`, or a field capacity that holds by a ceiling in its definition. No failure mode | no |
| `imp` | implied | the same inequality as a counted row, or an immediate consequence of counted rows (for example `g_j > 0` from `0 < kappa < G`) | no |
| `obs` | observation | outside both witnesses (the conventions observation) | no, and not in the verdict |

Every non-observation row enters the verdict: an identity or implied row that
failed would still fail the run. The parameter conditions are counted one per
stated comparison, and they overlap logically. For example, `2 eps < 1`
follows from `eps < 1/3`. The count measures the statements, not independent
facts.

Counts from `bun run check` (published witnesses):

| group | recomputed checks | parameter conditions | constants | lemma samples | identities | implied |
| --- | --- | --- | --- | --- | --- | --- |
| bit network (shared, B1 and B2) | 30 | 0 | 2 | 0 | 3 | 1 |
| 2^-59 witness (P1 to P5) | 26 | 33 | 2 | 0 | 5 | 13 |
| compact-control witness (C1 to C7) | 38 | 43 | 5 | 4 | 8 | 12 |

## What is checked, and against which statement

### Bit network, used by both witnesses

| group | rows | source statement | code |
| --- | --- | --- | --- |
| B1 | The local circuit at `n = 49` is rebuilt from the recursion in the prose: weighted pair blocks, coarse weights and edges, leave-one-out prefix and suffix sums, the four-term formula, direct sums at four or fewer vertices, interning, and removal of unused nodes. It has 9813 additions. `verifyCircuit.ts` takes only the addition list and the outputs. It recomputes every support and checks that every addition joins disjoint supports. It checks all 1271256 required coefficients and every required zero against `supp(z_cd) = {{a,b} : {a,b} ∩ {c,d} = ∅}`, and that no node is unused. | `paired-construction.tex`, sec:paired-bit-construction | `circuit.ts`, `verifyCircuit.ts` |
| B1 | Merge across the 50 common-point groups. A sum shared by groups `i ≠ j` is identified by `{i,j}` and its set of third points. This gives `c = 450394` and 40256 merged additions. For every group, the support of every reachable node is recomputed through the merged decompositions only. The checks: every partial output is exact, every addition is disjoint, every node's triples share a common point, every node has an outgoing use. `q = 58800` and `R = c + q = 509194` are identities applied to the recomputed `c` (not counted). | same, last paragraphs | `global.ts` |
| B1 | Frames reduce to support facts. Disjoint additions make `U_z` grow along every edge, so the orthogonal complement shrinks. A common point makes `U_z` nondegenerate, since `sum u_j = 3 u_i` and `<u,u> = sum_{j≠i} u_j^2` (tested on random spans). Exact outputs give `U_z ⊂ t_T^⊥`, a row marked implied. | "Reversible roles and frames" | `global.ts`, `test/circuit.test.ts` |
| B1 | The stage-1/stage-3 matching π is a bijection of the 19600 triples with `|A ∩ π(A)| = 1` and `<t_A, t_π(A)> = 0` for `I − J/9`. Constants: `h = 50 > 6`, `h ≠ 9`, and the exceptional eigenvalue `1 − h/9 = −41/9`. | same, matching paragraph; `03-motifs.tex` | `matching.ts` |
| B2 | `v, N, m, I, z_b`, original `W_b, s_b, L_b/N`, `W_b^pair = 2N + 2v^2(R+h)`, `s_b^pair = Wm − N + 6v^2h^2`, deficit 1767136000000, `eta_b = 23/661055000`. Then `m = 2^16 x`, `log m < 11737/1000` by the note's atanh partial sums with tail bound, and independently `e^(11737/1000) > m` by a Taylor partial sum. Finally `eta_b > a_b * 11737/1000`. | `03-motifs.tex` (patched to `h = 50`), `parameter-note.tex`, prop:paired-bit-interface, "Explicit exponents at ground size fifty" | `networks.ts`, `log.ts` |

### Current compact-control witness

| group | rows | source statement | code |
| --- | --- | --- | --- |
| C1 | `m_c = 15625`, `v_c = 2300`, `N_c`, `z_c = C(22,3) + 66`, `W_c = 2v^3 + 3v^2(v z_c + 26)`, `L_c = 3v^2·25·26`, `s_c = W_c m_c − 2N_c + 2L_c`, `eta_c = 14/3464399375`. `L_c < N_c` holds and `2L_c < N_c` does not; the note says only the first is needed. `log m_c < 966/100` by atanh, and independently `e^(966/100) > m_c` by Taylor. `eta_c > (418/10^12)(966/100)`. Constant: `h_c = 25 > 6`. | `independent-complex.tex`, prop:compact-complex-interface | `networks.ts`, `log.ts`, `checks.ts` |
| C2 | `1 − tau ≤ a_b = 296/10^11`. The bit saving is certified in B2. | `compact-control-note.tex`, sec. Scope | `checks.ts` |
| C3 | Parameter conditions: `0 < tau, sigma < 1`; `0 < beta < 1`; `zeta > 0`; `c, eps > 0`; `max{tau, sigma, chi} < lambda < lambda' < 1`; `max{sigma + beta(1−sigma), 1−c, 0} < lambda'`; `eps C1 < 1`; `eps < 1/3`; `2 eps < 1`; `eps(1−tau) < 1−tau`; `3/4 + delta + 5eps/4 < 1`; `eps(1+c) < 1`; `eps + delta < 1`; `0 < delta < 1/8`; the size exponents; `kappa < g_j` for each `j = 1..7`; `2^-34 < kappa < 2^-33`. Recomputed displayed values: `eps C1 = 99872039/10^8`, `chi_reserve = 4/5`, `alpha` exponent 11999/40000, `gamma` exponent 15997/20000, prime-interval exponent 3001/5000, `K` exponent 1999/50000, `ell` exponent 8001/10000, `G_* = g3 = 333833/(4·10^15)`, `G_* − kappa = 1833/(4·10^15)`. The closed-form margins agree with `1 − (row exponent)` of the patched cost table (an identity). | `compact-control-note.tex`, "Parameters and complete assembly"; `compact-control-layout.tex`, "Unrolling"; patch hunks for `05-layers.tex` and `08-assembly.tex` | `compact/witness.ts`, `parameters.ts` |
| C4 | Generalized guard with the complex network's own `m, W, s`: `m ≥ 3`, `2 ≤ s < m^5`. `E = 64(W+m+1)^3`, `B = s + E` and `C0 = ceil(max{128mB^2, 18mB^2(1+1/zeta)})` are recomputed (`C0 = 180018 m B^2` here). Condition: `C1 = 5 − 4beta + zeta`. The recurrence `A(e) ≤ sA(e/m) + E` internally, `A(e) ≤ 8e` at a leaf `e < d^beta`, is unrolled exactly at `d = m^K`, `K ∈ {250, 500, 1000, 1250, 2000}`. That is 5005 roots and up to 1999 internal levels. On each root, `j ≤ (1−beta) log_m d + 1` and `A ≤ s(8+E) d^(5−4beta)`. Identities, not counted: `s(8+E) ≤ 9B^2`, `9mB^2(1+1/zeta) + 18 ≤ C0`, `8d + ⌊D/2⌋ + 9 ≤ 18d`. Implied: `24W^3 + 4s + 4W + 4 < E` (from `0 < s < Wm`), `C1 ≥ 1`. | `compact-control-guard.tex`; `stopped-guard.tex` for the node charge | `compact/guard.ts` |
| C5 | Gaussian width at `eps = 1999/10000`. The cutoff `b ≥ 2^40` gives `46 b^(15997/20000) ≤ b/4`, compared exactly as `184^20000 ≤ 2^160120`. Constants: `(8√32)^2 = 2048 < 46^2` and `184 < 2^8`. Five concrete instances `b = 2^40, 2^41, 2^48, 2^64, 2^100` with `d = ⌊b^eps⌋` (integer root) and `alpha = ⌈(32db)^(1/4)⌉`. Each instance satisfies `alpha^4/(4d) ≥ 8b > 6b = p`, `alpha ≤ 2(32db)^(1/4)`, `gamma < 46 d^(3/2) √b`, `2 ≤ alpha < √p`, `gamma ≤ b/4` and `gamma < 46 b^(15997/20000)`. | `compact-control-note.tex`, sec. Parameters; patch `eq:gamma` | `gaussian.ts` |
| C6 | Scoped ceiling. The actual saving `a* = −log(1 − eta_c)/log m_c` is enclosed by a Mercator series for the numerator and atanh for `log m_c`, a different route from the Python. The checks: `a_c` lies below the enclosure; the enclosure rounds to the stated 4.1847990372e-10; `upper/5 < 8.369598075e-11`; the constant `8.369598075e-11 < 2^-33`; `kappa > (99/100)(upper/5)`; `⌊kappa·2^59⌋ = 47846242`. The chain `kappa < g3 = eps(1−lambda') < a_c/5` is marked implied. The symbolic part of the note's argument (`g5 > 0` forces `eps < 1/5`; the leaf condition forces `1 − lambda' < 1 − sigma`) is not a finite check; see the comment in `checks.ts`. | `compact-control-note.tex`, "Earlier targets and the next ceiling"; `docs/research/current-status.md` | `compact/ceiling.ts` |
| C7 | Lemma samples, which do not depend on the witness. The repair density `delta = n(2·2^-G + 8·2^(G−K)) ≤ 5/(128p^3)` holds at the cutoff `K = G + 4⌈log2 p⌉ + 10` with `n = p`, for every `p = 2..4096`. Constant: `2/64 + 8/1024 = 5/128`, the general step. The four-update identity holds for all `v, w ∈ [−40, 40]` and `z ∈ {0,1}`. For good digits `w ≤ B−2` the load stays in its digit and the displacement is at most `2B`. In the later-source composition the parities differ by exactly `x` and the temporaries are restored (`G = 1..4`). Identities, not counted: the layout capacities `2^(q0 K) ≥ W^k0`, `q_F K ≥ 2H`, `q_B K ≥ H`, `q_F + q_B ≤ 3dG/K + 2` on four instances `d = 10^3..10^30`. | `compact-control-movement.tex` ("Earlier source", "Later source", "Guards and deterministic repair", prop:compact-selected-addition); `compact-control-layout.tex` | `compact/layout.ts` |

### Preserved 2^-59 witness

| group | rows | source statement |
| --- | --- | --- |
| P1 | Complex network at `h = 50`: `z_c = 16356`, `W_c`, `s_c`, `L_c/N = 153/392`, `L_b, L_c < N/2`, `eta_c = 239/1202215191250`, `eta_c > (1/10^11)(11737/1000)`. Condition: `1 − tau ≤ a_b`. | `03-motifs.tex`; `paired-construction.tex`, "Explicit exponents" |
| P2 | 33 parameter conditions from the patched layer proposition, the assembly comparisons, the resampling lemma (`0 < delta < 1/8`), the size side conditions, and `0 < kappa < G`. Recomputed: `G = min g_j = 272158569/156250000000000000000000000`, `G = g2 = g3 = eps beta a^2`, `G < 2·2^-59`. The last shows that the old half-margin rule is not met, as the certificate records. Implied: `g_j > 0`, `lambda < 1`, and `G > 2^-59`. | `paired-note.tex` sec. 4; `h50-paired-59.patch` (`08-assembly.tex`) |
| P3 | Stopped guard, `beta = 999/1000`, `C1 = 2`: `m ≥ 3`, `2 ≤ s < m^5`, and `E, B, C0` recomputed. Conditions: `5 − 4beta ≤ 7/5` and `7/5 + 1/2 ≤ C1`. These are the note's own exponent facts: one piece has depth `9B^2 d^(7/5)`, and `2m√d` pieces give `d^(19/10) ≤ d^C1`. Constant: `36 < 128`. The unrolled recurrence holds on 47 roots, with up to 5 internal levels, against both `s(8+E) d^(5−4beta)` and `9B^2 d^(7/5)`. Identities: `s(8+E) ≤ 9B^2`, `18mB^2 + 18 ≤ 36mB^2`, `8d + ⌊D/2⌋ + 9 ≤ 18d`. Implied: `24W^3 + 4s + 4W + 4 < E`, and `beta ≥ 9/10` (the same inequality as `5 − 4beta ≤ 7/5`). | `stopped-guard.tex` |
| P4 | Gaussian width at `eps = 199/1000`: the stated `gamma` exponent `1597/2000` in both directions, the cutoff `184^2000 ≤ 2^16120`, the constant `2048 < 46^2`, and the same five concrete instances as C5. | `paired-note.tex` sec. 3; `eq:gamma` |
| P5 | Room left. The fixed-network ceiling `a^2/(5(1−a)) < 2^-58`, about `1.0133·2^-59`. The role budget: `R ≤ 509975` for `a_b = 296/10^11`. The largest savings on the `10^-11` grid: 296 (bit) and 1 (complex). | `docs/research/paired-network.md` |

## The review guide's "Exact witness and scoped ceiling" items

| item in `compact-control-review.md` | where | status |
| --- | --- | --- |
| seven margins and `min(g_1..g_7) = 333833/(4·10^15)` | C3: `kappa < g_j` for each `j`; `G_* = g3`; `G_* = 333833/(4·10^15)` | recomputed |
| `kappa = 83/10^12` | C3: input of the note; all conditions hold for it | input |
| `min(g_i) − kappa = 1833/(4·10^15) > 0` | C3 | recomputed |
| `2^-34 < kappa < 2^-33` | C3 | condition on the input |
| complex network counts at `h = 25` | C1 | recomputed from the formulas (construction not rebuilt) |
| `a_c = 418/10^12` with a rigorous log enclosure for `m_c = 15625` | C1 (atanh and Taylor, `log m_c < 966/100`); C6 (Mercator and atanh enclosure of the actual saving) | recomputed by three routes |
| generalized guard `C1 = 5 − 4beta + zeta` | C4 | constants recomputed; `C1` a condition |
| scoped ceiling `8.369598075e-11`, witness above 99% of it | C6 | recomputed |
| "about 47.85 million times" the `2^-59` saving | C6: `⌊kappa·2^59⌋ = 47846242` | recomputed |

## The review guide's new obligations

The review guide lists eight new obligations. A finite arithmetic checker can
cover only their numerical parts.

| obligation | what this checker covers | what it does not cover |
| --- | --- | --- |
| Controls wider than a rotation target (`lem:record-paid-rotation`) | nothing | A tape-time bound on a multitape machine: counters, resets and offset work paid by `O(V + M A^C)`. **Outside any arithmetic checker**; it is a proof about the machine model. |
| Dirty compact controls | the four-update identity, digit loads without overflow for good digits, the displacement bound, and later-source parity and restoration, all on samples (C7) | The packed modular address maps, swaps, control order and both source orders as maps on the full rectangle. Finite instances could be simulated, and `scripts/audit_compact_controls.py` samples them; this checker does not. The general statement is a proof. |
| Deterministic exceptional repair | the density bound `delta ≤ 5/(128p^3)` at the cutoff (C7 sample, plus `compare` on the certificate's four instances) | Bad-set invariance, `S = T` off the bad set, inverse offsets and the sort. Finite instances could be simulated (not here). The general statement and its fixed-tape cost are **outside any arithmetic checker**. |
| Existing-coordinate temporaries (layout) | the capacity formulas (identities) on four instances; `compare` recomputes the certificate's three allocations | That full ranges survive every recursive row split, that no hidden volume appears, and the small-`D` fallback. An invariant over all recursion depths and all `p, d`: **outside any arithmetic checker**. |
| Recursive cost | the exponent algebra: `chi`, `chi_leaf`, `chi_reserve` against `lambda < lambda'` (C3) | The recurrence `F(e) ≤ (s/W)F(e/m) + O((e log p)^tau + 1)` itself: exact `V/W` child volumes, spectator layout, uniform constants. **Outside any arithmetic checker.** |
| Precision (generalized guard) | `E, B, C0, C1`, the finite comparisons, and the unrolled recurrence on samples (C4) | That the new operations only permute whole coefficient encodings, and that every reserved kernel and base-`m` piece is counted. These are structural claims about the algorithm (**outside**). The analytic step `log d ≤ d^zeta/zeta`, behind the piece count `m(1+1/zeta) d^zeta`, is not checked here. |
| Independent complex arity | counts, `eta_c`, `log m_c`, the saving and its enclosure (C1, C6) | Residual nondegeneracy, norm-one witnesses, scalar restoration, endpoint corrections, and the absence of a hidden equal-arity requirement. At fixed `h = 25` the first two are finite linear algebra that a larger checker could do; this checker does not build the complex network. The last is a reading of the proof (**outside**). |
| Final assembly | the seven margins, the strict gap, and the agreement of the closed-form margins with the patched cost table (C3) | That every changed cost enters the completed-layer estimate, and that the cost table is complete. **Outside any arithmetic checker.** |

## `bun run compare`

`compare` reads each certificate with a parser that keeps every integer exact.
`JSON.parse` would round them, and `compact-control-layer.json` stores integers
of up to 118 digits as bare JSON numbers. It assigns every leaf field exactly
one status, and it refuses to report if any field is unclassified or
classified twice:

- **recomputed**: the TypeScript value, computed from the note's inputs, equals the certificate's.
- **recomputed\***: the same, but the instance's inputs (`d, D, K, G` of a
  layout instance, `p, n, K` of a repair instance, a milestone's parameters)
  were read from the certificate, because no note states them.
- **input**: the field is one of the note's inputs, or follows from them by a
  fixed allocation. Agreement only shows that both sides used the same inputs.
- **other method**: the same claim is established differently, so only the
  conclusions are compared. This covers the two frame flags, where the
  TypeScript uses the support-level argument and the Python checks every role,
  and the complex-saving enclosure and scoped ceiling, where Mercator and
  atanh replace the Python's atanh on `1/(1−eta)`.
- **not compared**: with the reason (descriptive strings, the Python's circuit hashes, instance inputs).

| certificate | leaf fields | recomputed | recomputed\* | input | other method | not compared | differ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `paired-network.json` | 129 | 74 | 0 | 37 | 2 | 16 | 0 |
| `compact-control-layer.json` | 277 | 53 | 108 | 30 | 4 | 82 | 0 |

Notes on the counts:

- The 74 recomputed fields of `paired-network.json` include 18 constraint
  slacks. Each slack is arithmetic on the stated parameters, not a new
  quantity.
- The 53 recomputed fields of `compact-control-layer.json` include 19 constraint slacks
  and the four `proof_sha256` hashes of the notes. The hashes check file
  integrity in this checkout, not mathematics.
- `complex_log_upper` is recomputed with the 24-term atanh enclosure. That is
  the method of the paired note and of the Python, so its agreement is not an
  independent confirmation; the Taylor and Mercator routes are.

## Failure tests

`bun test` runs 339 tests in seven files. The repository asks for tests that
address an identity or a failure mode. Each test here either checks an
identity with a closed form or feeds real checker code an input that must be
rejected:

- `circuit.test.ts`: the real verifiers receive small corrupted objects and
  must reject them. A local output with one extra input term. An output that
  sums one input twice: its support is right as a set, so only the
  disjointness flag catches it. A global graph with one output pointer swapped
  (exactness and orthogonality fail). An output with an extra triple meeting
  its target in two points. A node without a common point. A matching π that
  is not injective, cycles over all pairs, or is the identity.
- `downstream.test.ts`, `compact.test.ts`, `each-check.test.ts`: every listed
  inequality, given an input just past its limit, fails by name.
- `runner.test.ts`: the rows that `bun run check` actually prints and counts
  are tested where `src/checks.ts` produces them. A misstated note value, a
  parameter past its limit, a different ground size, or a verifier report with
  one flag false must make the named row fail. A completeness test then
  requires that **every counted row** is either made to fail by one of these
  cases or appears in `NOT_RUNNER_FAILABLE` with the function-level test that
  makes its underlying computation fail. It also requires every named row to
  be present. Deleting, renaming or weakening a counted row at its boundary
  therefore fails a test. `NOT_RUNNER_FAILABLE` holds three kinds of row:
  `m ≥ 3`, `2 ≤ s < m^5` and the depth samples, for which no admissible ground
  size gives a failure; the constants `h = 50` admissible, `36 < 128`,
  `184 < 2^8` and `2/64 + 8/1024 = 5/128`; and the four lemma samples.
  A test also spawns `bun run check` with one nudged parameter per witness and
  expects exit code 1.
- `compare.test.ts`: corrupted certificates (one value changed, a frame flag
  false, a scoped ceiling below the true value, a wrong source hash, an extra
  or a missing field) must give `DIFFER` or a refusal.

**Mutation testing.** 57 single changes were applied to the source in a
scratch copy, and `bun test --bail` was run after each. The changes made
verifier flags unable to fail, removed π's bijectivity or triple check,
weakened `<` to `<=` at the boundary of the listed inequalities, deleted
`kappa < g3`, replaced stated values by the recomputed ones, ignored the
`(1 − beta)` factor in `chi`, dropped enclosure tails, moved the repair cutoff
by one, forced exit code 0, and made the comparator agree with everything.
56 were caught. The one survivor weakens the identity `s(8+E) ≤ 9B^2`. No
admissible input can make that row fail, so it is labelled an identity and
not counted.

## Provenance of the key quantities

| quantity | provenance |
| --- | --- |
| 9813 local additions; `c = 450394`; 40256 merged | recomputed by building the circuit (under the conventions below) |
| `q = 58800`; `R = c + q = 509194` | identities applied to the recomputed `c` (`q = h·C(h−1,2)`; `R = c + q` is the note's role count, not rederived) |
| `W_b^pair`, `s_b^pair`, `eta_b` | recomputed from `prop:paired-bit-interface`'s formulas with the recomputed `R`; the formulas themselves are inputs from the note |
| `a_b = 296/10^11`, `a_c = 418/10^12`, `eps, c, beta, zeta, delta, C1, lambda, lambda', kappa` | inputs from the notes; checked against every stated condition |
| `log m < 11737/1000`, `log m_c < 966/100` | recomputed by two methods each |
| complex counts at `h = 25` and `h = 50`, `eta_c` | recomputed from the upstream formulas (construction not rebuilt) |
| `E, B, C0` (both guards) | recomputed |
| `g_1..g_7`, `G`, `G_*`, absorption gaps | recomputed from the inputs; the margin formulas are inputs from the patched cost table, transcribed twice |
| actual complex saving `a*` and the scoped ceiling | recomputed by a method different from the Python's |

## What is not checked

- The upstream algorithmic theorem: the multitape model, tape-movement costs,
  recursion, the analytic resampling lemmas, prime selection, synthetic
  transforms and final rounding. These are assumptions of the repository.
- The algorithmic content of the new extensions. That is everything marked
  outside in the obligations table above. It includes the wider-control tape
  bound, the recursive layout invariant, the repair procedure as a map, the
  recurrence itself, and the completeness of the assembly accounting.
- The packed modular address permutations, swaps, inverses and the repair
  sort, which are not simulated. `scripts/audit_compact_controls.py` samples
  them in Python.
- Neither complex network (`h = 25` or `h = 50`) is rebuilt; only its counts
  are recomputed. Its residual bases, norm-one witnesses, scalar schedule and
  endpoint corrections are not checked.
- The role accounting of the full three-stage bit network is taken from the
  statement of `prop:paired-bit-interface`, not rederived. That includes
  `W = 2N + 2v^2(R+h)`, with `2v^2` from stage-1/stage-3 sharing, and
  `s = Wm − N + 6v^2h^2`. No rational matrices are formed, and neither the
  scalar schedule nor the restoration of dirty scratch is simulated.
- The cost-table rows (which operation costs `dK`, `d(1 + ell^tau)` and so on)
  are taken from the patched text. Only their exponent arithmetic and their
  agreement with `g1..g7` are checked.
- Analytic steps are not checked. These include `log d ≤ √d` (2^-59 piece
  count), `log d ≤ d^zeta/zeta` (compact piece count), `K ≥ d^c/2` for large
  `p` (true on the instances), and the eventual error terms that the patches
  bound by `10^-3` beyond `b ≥ 2^40`. Of the cutoff conditions, only
  `gamma ≤ b/4` is checked.
- The milestone parameter sets (`target_34`, `target_39`) are checked only
  inside `compare`, with their parameters read from the certificate, because
  no note states them.
- The certificates' `circuit_sha256` values, which hash the Python's own
  encoding of node ids.

## Independence caveats

- **Written from the notes and patches:** the circuit recursion, the merge
  key, the frame reduction, π, the network counts, both guards, the Gaussian
  instances, the Taylor and Mercator routes, the depth-recurrence samples and
  every failure test.
- **Leaning on the Python, bit network:** the zero-terms summation convention
  (see the next section) was found only by comparing node lists with
  `scripts/paired_exclusion_circuit.py` after the counts disagreed. The
  certificate's `constraint_slacks` names were mapped to these checks after
  the list had been compiled from the notes. The JSON format was read to
  write `compare.ts`.
- **Leaning on the Python, compact-control witness:** the helpers in
  `src/compact/layout.ts` (`allocation`, `repairBound`, `ceilLog`) have the
  same signatures, the same field names in the same order, and the same
  `mode` rule as `allocation`, `repair_bound` and `ceil_log` in
  `scripts/compact_control_layer.py`. `layerExponents` in
  `src/compact/witness.ts` has the same `theta` parameter as
  `packed_exponents` in `scripts/prepare_layers.py`. That parameter models
  the earlier wide-slot overhead and is used only in a test. The session that
  wrote these files was interrupted, and its record does not show which
  files it opened. The structure suggests those Python files were consulted.
  Their formulas were then checked, by reading, against
  `compact-control-layout.tex` ("Rows and complete compact fields" and
  "Unrolling") and `compact-control-movement.tex` ("Guards and deterministic
  repair"), and they agree. Still, these helpers should not be presented as
  written independently of the Python.
- **Same method as the Python, because the note prescribes it:** the 24-term
  atanh enclosure of `log m` (paired note). It is also used for `log m_c`,
  for which the new note names no method. The Taylor route (`e^L0 > m`) and
  the Mercator route for the complex saving are different methods.
- **Shared reading:** both implementations read the same upstream text, so a
  misreading common to both would not be caught.

## Conventions: what the circuit prose leaves open

`notes/paired-construction.tex` fixes the algebra of the paired-block circuit,
but not every summation order, and with interning the number of additions
depends on the order. The prose leaves three choices open:

- where balanced binary addition splits a list of `k` terms (`⌊k/2⌋` or `⌈k/2⌉`);
- whether zero terms (the empty weight of the final singleton block) take part in the split;
- the term order in the direct sums at four or fewer vertices.

The published counts correspond to the choices fixed by
`scripts/paired_exclusion_circuit.py`: floor split, zeros kept, edges before
weights. With them, this checker reproduces 9813 local additions,
`c = 450394` and `R = 509194`. Another reading is ceiling split, zeros
dropped, weights before edges. It gives a circuit with 9810 local additions,
`c = 450244`, 40256 merged additions and `R = 509044`. That circuit passes
this checker's local and global support checks (row `B0`, an observation
outside both verdicts). It also passes the repository's own verifiers at
`h = 50`: `verify()`, `verify_embedding()`, `SharedPointCircuit.verify()` and
`verify_frames()`. At `h = 6` and `h = 8` it also passes `exact_invocation`.
These Python results were re-run against commit 6e56487.

The alternative does not change `G` or `kappa` in either witness. With
`R = 509044`, `a_b = 297/10^11` still fails `eta_b > a_b L0`, which would need
`R ≤ 508192`. And the compact-control minimum `G_* = g3 = eps(1 − lambda')`
does not depend on `a_b` at all.

This is an observation about the prose, not a correction. The published count
is not wrong: it is the count for the conventions the script fixes. Nothing
here shows that 509044 is minimal. The alternative was not run through the
full three-stage invocation or the dirty-scratch checks at `h = 50`. And, as
said, it does not improve `kappa`.

## Disclosure

This code, its tests and this README were written by Claude (an AI model by
Anthropic) in Claude Code sessions directed by the submitter (@fernandoeeu),
a software engineer who is not a specialist in this mathematics. Separate
agent sessions wrote the first version, reviewed it from a fresh context,
extended it to the current witness, and ran the mutation tests described
above. That is not independent review: at the time of submission no human
has audited the mathematics or read the code line by line.

It is contributed under the repository's Apache-2.0 license. Passing these
checks is not a formal verification of the multiplication theorem.
