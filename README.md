# The GF(2) Möbius transform below N log N

**Swapnil Jain. Preprint-stage; checked by AI agents only, not human-refereed; asymptotic only.** "X1" is this project's internal name for the construction; it appears in file names and headings.

Let S = [[1,0],[1,1]] and M_k = S^{⊗k}: the Möbius (zeta, Sierpinski) transform over GF(2) on N = 2^k inputs. Yates'
algorithm computes it with (1/2) N log₂ N XORs. We claim (not human-refereed, asymptotic only; crossover log₁₀ k ≳ 6.9·10⁹) that its XOR-circuit complexity, for fan-in-2 circuits that are
allowed to cancel, is

  **L_{F₂}(M_k) = O(N (log N)^{θ′}), with θ′ < 1**, so L_{F₂}(M_k) = o(N log N).

Three versions are proved, all under the same proved recursion (`proofs/PROOF.md`, Thm 2.6′: one directional step per
kernel, roles padded to a power of 3):

| | Gadget and exceptional route | 1 − θ′ | h, W* | Review |
|---|---|---|---|---|
| **Theorem 1** | 4-subset F₃ labels, Lucas centre \|P\| ≤ 2, one correction kernel per bank entry | **1.8309·10⁻¹⁵** | 92, 3⁵⁵ | refereed twice, by independent AI agents |
| **Theorem 1′** | the same, with the two-sided monomial pre-pass in place of the correction kernel | **4.2213·10⁻¹³** | 51, 3⁴⁶ | the pre-pass refereed once, by an AI agent |
| **Theorem 2** | E1: 7-subset F₃ labels, centre of 3-subsets (C(n,3) mod 2), side wires on J-supported pairs only, with the pre-pass | **4.3713·10⁻¹¹** | 23, 3⁴⁵ | refereed once, by an AI agent; no full 7-set network has been run |

**Crossover with Yates.** By `proofs/PROOF.md` §8, log₁₀ k ≈ log₁₀ m · ln c₀/ε, with each row's own m = h³ and
ε = Δ/(W*m). c₀ is the ratio of constant factors; c₀ = 84 is the explicit constant of the word.

| c₀ | Theorem 1 | Theorem 1′ | Theorem 2 |
|---|---|---|---|
| 2 | 1.6·10¹⁴ | 7.1·10¹¹ | 6.9·10⁹ |
| 84 | 1.05·10¹⁵ | 4.6·10¹² | 4.4·10¹⁰ |
| 10⁶ | 3.3·10¹⁵ | 1.4·10¹³ | 1.4·10¹¹ |

These are values of log₁₀ k, not of k. **Every result here is asymptotic only.** No feasible size beats Yates, and
nothing is witnessed at any feasible size.

**Open (a conjecture, not a theorem).** A faster "whole-residual batching" recurrence, with one C′^{⊗ρf} call per residual
of dimension ρ, would give 1 − θ ≈ 3.98·10⁻⁹ for Theorem 2's gadget. That recurrence is not proved, the figure is unpadded,
and nothing in this repository depends on it (`proofs/PROOF.md` §11).

**Working on this problem?** Read [docs/CLOSED_IDEAS.md](docs/CLOSED_IDEAS.md) first. It lists routes we tried that do not
work, each with its reason and scope.

## Credits

- **The construction is from the openai/math explicit-DFT preprint**, "An explicit power saving for the exact discrete
  Fourier transform", by OpenAI (its listed author; openai/math, problem 130; per their README, the openai/math material was "produced by an internal OpenAI model"). We use its architecture: the eight-row
  network, the three stages, the label table, the frames and kernels, and the recurrence that batches the fibres of each step (its Thm 2.6). Its proof is over ℂ.
  No statement of the preprint is used as a hypothesis here: every step we use is re-proved in the flipped setting.
- **Context.** Joan Boyar and Magnus Gausdal Find (arXiv 1207.5321, 1305.3041) proved that (1/2) N log N is tight for
  cancellation-free circuits for this matrix, and asked to what extent cancellation can help. Igor Sergeev lists L(D_n) < n·2^{n−1} as an open problem and gives the lower bound (3 − o(1))·2^n, as stated in his 2024 slides (paper: Math. Notes 118, 2025).
- **Ours:**
  - the characteristic flip: F₃ labels, F₄ and F₁₆ data, the Lucas centre mod 2, and the correction kernel;
  - the two-sided monomial pre-pass (Lemma 6.1), which removes the correction kernel;
  - the E1 gadget (§10);
  - the written re-proofs in `proofs/PROOF.md`;
  - the explicit 12-slot F₁₆ word (`proofs/WORD.md`);
  - the transfer to F₂;
  - the machine checks: the scripts in `certificates/` and the Lean modules in `lean/`.

See [NOTICE](NOTICE) for the full list of sources.

## 1. How it works

- **Flip the characteristic.** The preprint uses F₂ labels with complex data. Here the characteristics are swapped: the labels
  live in F₃ and the data in F₄, with ω³ = 1. The kernel becomes C′ = ωI + ω²J₃, and the frames
  Φ_U = F·D_{ω^{Q(P_U y)}}·F⁻¹ telescope through the network as in the preprint.
- **The centre.** The F₂ gadget needs RG + JV = I. With 4-subset labels and a centre of all subsets of size ≤ 2,
  RG = 1 + n + C(n,2) mod 2 (Lemma 1.2). With 7-subset labels and a centre of 3-subsets, RG = C(n,3) mod 2, which vanishes
  on the disjoint pairs that dominate the wire count (Lemma 10.1).
- **The exceptional route.** The bank route X_d → Y_d carries the ratio R_u = Φ_{U^⊥}Φ_U⁻¹. Theorem 1 corrects it with one
  extra directional step. Theorems 1′ and 2 instead write R_u = M₁·C′^{⊗m}·M₂ with monomial M₁ and M₂: an isometry
  A with Au = e₁, built from two reflections, plus Lemma 3.4's Frob(C′) = D·P₂₃·C′·D. They feed M₂⁻¹x into X_d and read
  M₁⁻¹ of Y_d. This saves one step per bank entry, so μ = 2 and the saving per level becomes Δ = 2v²(v − 3ch).
  **Gotcha:** an output-side monomial alone cannot do this (it works for 0 of the 42 lines checked); the adapter must be two-sided.
- **Recursion and transfer.** Thm 2.6′ batches the fibres of each step into the W*-array algorithm, which gives
  t(k) ≤ A + λ′·t(k/m). An explicit 12-slot word writes S⊗S with C′⊕1 over F₁₆. Sectors and Jensen bound the cost of
  (C′⊕1)^{⊗t}, and every F₁₆ gate descends to at most 28 XORs.

## 2. Status: what is proved, checked, Lean-checked

| Item | Status |
|---|---|
| §§1–8 (Theorem 1) | Written proof, every step tagged [proof], [arg] or [cite]. Two independent AI referees: CONFIRMED WITH FIXES, with no claim-level defect. Their fixes are applied. |
| Lemma 6.1, the pre-pass (Theorem 1′) | Written proof. One AI referee confirmed it and found an overclaim in our earlier exponent, now corrected (CORRECTIONS.md). Checked on the Fourier side for all 42 norm-1 lines with m ≤ 4, f ≤ 2, and in a real network (configs A and B: every role correct, with s′ − N₀ steps). One-sided controls fail. |
| §10, E1 (Theorem 2) | Written proof, reusing §5's cell structure. One AI referee. Lemma 10.1 is proved in Lean for every finite type. One scalar invocation is executed at h = 11 and 12, with two controls (`x1_e1_check.py`). Full-network check at h = 8–11: scalar network (all invocations at h ≤ 10), brute-force F₃ edges on representative invocations, the d* bank path with the pre-pass, orbit-weighted count = closed form, 0 failures; both controls refuted (`x1_e1_rep.c`). |
| The count at large h | Re-derived from Lemma 5.1's cell tables (`x1_exponent_count.py`, `x1_theorems.py`). It is checked against brute-force F₃ linear algebra at h = 6–10 only, so it is not independent evidence at h = 23, 51 or 92. |
| Real-array tests | Toy data, m ≤ 6. The genuine families have m ≥ 125 and are infeasible on arrays. |
| Lean (`lean/`) | Lean 4 kernel checks: Mathlib, standard axioms only, no `sorry`, no `native_decide`. They cover the numeric core of all three theorems and the two centres (table below). Not in Lean: the network lemmas, the recursion and the transfer. |
| Novelty | `docs/NOVELTY.md`. We find no prior o(N log N) claim, nor any claim below (1/2) N log₂ N, for XOR circuits with cancellation. Confidence is about 90%. |

### What the Lean package checks

| Module | Statement |
|---|---|
| `Numeric` | Theorem 1: v, c, d, m and W at h = 92; W* = 3⁵⁵; Δ′ = v²(v − 6ch) > 0 on [79, 92] and < 0 at 78; the ε′ bounds; θ′ < 1; 1 − θ′ ∈ [1.830916303, 1.830916304]·10⁻¹⁵ |
| `Lucas`, `Brute` | Lemma 1.2 for every h (Finset proof); RG + JV = I on bitmasks at h = 6, 7; the counts by enumeration at h = 8–10 |
| `Word` | F₁₆ arithmetic; C′³ = I; Frob(C′) = D·P₂₃·C′·D; the 27 slots multiply to exactly S⊗S |
| `DefsPrepass`, `Prepass` | Δ = 2v²(v − 3ch) for both families (closed form). Signs: positive on h ∈ [43, 120] and negative on [4, 42] for 4-subsets; positive on [20, 60] and negative on [7, 19] for E1. Exact values and W* = 3⁴⁶ (h = 51) and 3⁴⁵ (h = 23). θ′ < 1, θ′ > 0. **1 − θ′ ∈ [4.22128277, 4.22128278]·10⁻¹³** (Theorem 1′) and **[4.37127524, 4.37127525]·10⁻¹¹** (Theorem 2), from rigorous series bounds on log. |
| `LucasE1` | Lemma 10.1 for every finite type: #{P ⊆ S∩T : \|P\| = 3} = C(n,3); C(n,3) is odd exactly at n ∈ {3, 7}; for 7-subsets, the diagonal is odd, non-neighbours are even, neighbours with \|S∩T\| ∈ {0, 6} are even, and \|S∩T\| = 3 is odd |
| `Controls`, `ControlsLight`, `ControlsPrepass` | **Refuted controls**, each proved false. They include: thresholds shifted by one (h = 78, 42, 19); E1 without the pre-pass at h = 20; one power of 3 fewer roles; ε and 1 − θ′ bounds moved by one digit; a centre of size ≤ 1; a 2-subset centre and the \|P\| ≤ 2 centre on 7-sets; no J; neighbours taken mod 2; a wrong neighbour count; one changed word entry; a changed D₄ |

## 3. Reproduce

Requires Python 3.9 or newer and a C compiler. Only `x1_real_arrays.py` needs numpy (`pip install -r requirements.txt`;
tested with 2.0.2), and the tests skip it when numpy is missing. Every other script uses the standard library only.

```sh
make check   # every certificate and check, through tests/ (about 2 minutes, under 400 MB)
make lean    # the Lean 4 kernel checks and the axioms audit (lean/README.md: elan with Lean v4.34.1, Mathlib cache)
```

| Script (`certificates/`) | Checks |
|---|---|
| `x1_theorems.py` | The three rows: closed form against the cell walk, sign thresholds, the best h, ε, 1 − θ′ and the crossovers. `--conjecture` also prints the unproved batching value, labelled as a conjecture. |
| `x1_prepass_check.py` | Lemma 6.1 on the Fourier side, for 42 lines, with the one-sided control |
| `x1_e1_check.py` | Lemma 10.1 and one E1 invocation at h = 11 and 12, with a 2-subset-centre control and a no-J control |
| `x1_e1_rep.c` | E1 full-network check (Theorem 2): scalar network, brute-force F₃ edges on representative invocations, the d* bank path with the pre-pass, and the orbit-weighted count at h = 8–11; logs `run_e1_rep_h{8,9,10,11}_bad0.txt`, `run_e1_rep_h11_bad1.txt`, `run_e1_rep_h12_bad2.txt` |
| `x1_exponent_count.py` | Theorem 1: the count at h = 79–92, and agreement with brute force at h = 6–10 |
| `x1_e2e_rep.c`, `m5_xref_e2e.c` | The scalar network over all invocations, plus brute-force F₃ linear algebra on every edge (h = 6–10) |
| `x1_real_arrays.py` | Prop 2.4′ on real F₄ arrays. Mode 4 runs the pre-pass; mode 5 is its one-sided control. |
| `x1_word_check.py`, `m6_word_*` | The F₁₆ word, checked twice by independent code; the word search; the crossover constant |

Saved logs are the `run_*.txt` files. `tests/test_certificates.py` runs each script and checks its printed values.

## Further notes

- [docs/RESULT.md](docs/RESULT.md): status, and how each referee's gap was closed.
- [docs/NOVELTY.md](docs/NOVELTY.md): the literature check, with citations.
- [docs/CLOSED_IDEAS.md](docs/CLOSED_IDEAS.md): routes that do not work, each with its reason and scope.
- [CORRECTIONS.md](CORRECTIONS.md): dated corrections.

## Attribution

Author: **Swapnil Jain**. Research, implementation and drafting were done with assistance from Claude (Anthropic).
AI assistance is not independent review. Licensed under Apache-2.0.
