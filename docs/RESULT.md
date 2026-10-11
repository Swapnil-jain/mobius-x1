# X1 result (2026-10-11)

**Status: claimed; proofs written and checked by AI agents only; no human referee.** No statement of the openai/math preprint is used as a hypothesis: the preprint supplies the architecture, and every step used is re-proved in `PROOF.md`. (Earlier wording, "modulo the preprint", understated this.) All of it is agent-written and agent-checked. **No human has refereed it.**

- Every step of the preprint that X1 uses has been re-proved in the flipped setting, with a [proof] tag, in `PROOF.md`.
- The only preprint item still cited is Lemma 2.5 (RAM-model address permutations). The circuit model does not use it.
- The generation step now rests on an explicit, independently re-verified word, so Ostrom–Wagner is no longer cited.
- Claim: **L_{F₂}(M_k) = O(N (log N)^{θ′})**, in three proved versions under the same recursion (Thm 2.6′):

| | Gadget and route | 1 − θ′ | h, W* | Crossover log₁₀ k (c₀ = 2 / 84 / 10⁶) | Review |
|---|---|---|---|---|---|
| **Theorem 1** | 4-subset labels, correction kernel | **1.8309·10⁻¹⁵** | 92, 3⁵⁵ | 1.6·10¹⁴ / 1.05·10¹⁵ / 3.3·10¹⁵ | refereed twice (AI agents) |
| **Theorem 1′** | 4-subset labels, two-sided pre-pass (Lemma 6.1) | **4.2213·10⁻¹³** | 51, 3⁴⁶ | 7.1·10¹¹ / 4.6·10¹² / 1.4·10¹³ | pre-pass refereed once (AI agent) |
| **Theorem 2** | E1: 7-subsets, 3-subset centre, pre-pass (§10) | **4.3713·10⁻¹¹** | 23, 3⁴⁵ | 6.9·10⁹ / 4.4·10¹⁰ / 1.4·10¹¹ | refereed once (AI agent); no full 7-set network run |

- **Honest note.** Every crossover is far beyond any feasible size (PROOF.md §8's formula, log₁₀ k ≈ log₁₀ m · ln c₀/ε, each
  row with its own m and ε). Nothing is witnessed at any feasible size. These are asymptotic statements only.
- **Open, a conjecture only.** A whole-residual batching recurrence (one C′^{⊗ρf} call per residual) would give
  1 − θ ≈ 3.98·10⁻⁹ for E1 with the pre-pass. It is not proved, and no theorem here uses it (PROOF.md §11).

## The referees' gaps, one by one

| Gap | Status | Evidence |
|---|---|---|
| (a) h = 6 run not reproducible; scalar stand-in | **Closed.** Reproduced the h = 6 run, and extended the checks to h = 7–10 plus real arrays. | `m5_xref_e2e.c` (in `certificates/`): 0 failures, 22 336 425 steps = closed form, 146 s, 115 MB. Its control bad=2 fails only on Y_d (6 777 / 13 500 here; the first referee's run reported 6 779, a libc rand difference). `x1_e2e_rep.c` at h = 6, 7, 8, 9, 10: details below. |
| (b) no recursion level with f ≥ 2 on real arrays | **Closed for admissible toy data. Infeasible for the genuine family.** | The smallest genuine case has m = 125, so one column is 3¹²⁵ entries. `x1_real_arrays.py` executes Prop 2.4′ on real F₄ arrays (details below). |
| (c) flipped lemmas have no written proof | **Closed** (written, not human-refereed). | `PROOF.md` §§1–7: Lemma 1.2, Lemma 2.1′, Lemmas 2.2′ and 3.1–3.4, Lemma 4.1, Lemma 5.1 and 2.3′, Prop 2.4′, Thm 2.6′. All are stated for general admissible data. |
| (d) h ≥ 79 only extrapolated | **Closed as a re-derivation** (not independent of Lemma 5.1). | `x1_exponent_count.py`: an exact edge-by-edge count at every h from 79 to 92, with v, d_nbr and c enumerated (details below). Brute-force F₃ algebra in F₃^{h³} at h ≥ 79 is infeasible, since m ≥ 4.9·10⁵. |
| (e) explicit generation word missing | **Closed** (found by our own search, `m6_word_search.py`; re-verified here). | A 12-slot word for S⊗S, `WORD.md` (in `proofs/`, with its `m6_word_*` scripts in `certificates/`). `x1_word_check.py`, independent code, confirms it exactly over F₁₆ and checks the mixed product at t = 2. |

**Details for (a): `x1_e2e_rep.c` at h = 6, 7, 8, 9, 10.**
- The scalar network was run over all invocations; at h = 10 that is 18.5M bank checks, with 0 failures.
- On representative invocations, every edge was done by brute force in F₃^{h³}. That covers |∩| = 1 non-neighbours (h ≥ 7) and
  disjoint neighbours (h ≥ 8), with frame phases cross-checked: 0 failures.
- The orbit-weighted exact step count equals the closed form at every h, and equals the full brute force at h = 6.
- Controls fail as expected:
  - a wrong row-5 label gives 765 nesting failures;
  - a centre of size ≤ 1 gives 64 541 swap failures.

**Details for (b): `x1_real_arrays.py`.** It executes Prop 2.4′ on real F₄ arrays. Every edge is address change + C'^{⊗f} on
fibres + inverse change; inverse kernels are executed as D·P₂₃·C'·D. Every role, auxiliaries included, is compared with Yates
C'^{⊗mf}.
- **Config A** uses the genuine 4-subset family of [6] with the genuine Lucas centre in factor 1: m = 6, f = 2, 3¹² entries,
  W = 808. It gives 0/808 failures and 6 084 steps = s′ (109 s, 328 MB).
- **Config B** has B ≠ 0 with side wires: m = 4, f = 2 and f = 3. It gives 0/138 failures.
- Controls fail as expected:
  - no correction gives 18/18 Y_d failures;
  - a wrong label gives 60 nesting failures;
  - a bad centre gives 60/60 X_d failures.

**Details for (d): `x1_exponent_count.py`.**
- The count, re-derived edge by edge from Lemma 5.1's cell tables (not independent of that lemma), equals Wm − N₀ + 2I₀ch at every h from 79 to 92. The script compares the same bookkeeping with brute force at h = 6–10 (per stage, d* path, total): all match.
- Δ′ > 0 for 79 ≤ h ≤ 92, and Δ′ < 0 at h = 78.
- The best h is 92, with ε′ = 2.4837·10⁻¹⁴ and 1 − θ′ = 1.8309·10⁻¹⁵ (h = 93–120 checked by closed form only).
- The cell bookkeeping agrees with brute force at h = 6–10.

## The pre-pass and E1 (added 2026-10-11)

- **Pre-pass (Theorem 1′).** The exceptional route's correction kernel is replaced by a monomial on both sides of the
  network (PROOF.md Lemma 6.1, Prop 2.4′). This gives μ = 2 and Δ = 2v²(v − 3ch). An independent referee confirmed it.
  It is checked on the Fourier side for 42 lines (`x1_prepass_check.py`) and in a real network (`x1_real_arrays.py`
  mode 4, configs A and B, every role correct, steps = s′ − N₀). A one-sided adapter fails 0/42 and 18/18 (controls).
- **E1 (Theorem 2).** 7-subset labels, 3-subset centre, side wires on |S∩T| = 3 pairs only (PROOF.md §10). The centre is
  checked in Lean for every h, and one invocation is run at h = 11, 12 (`x1_e1_check.py`). Full-network check at h = 8–11
  (`x1_e1_rep.c`): scalar network over all invocations at h = 8, 9, 10 and one representative invocation per stage at
  h = 11; brute-force F₃ linear algebra on every edge of the representative invocations (nondegeneracy, nesting,
  residual, orthogonal basis, phase); the d* bank path with the pre-pass (μ = 2, no correction kernel); the
  orbit-weighted exact step count equals the closed form Wm − 2N₀ + 2I₀ch at every h; 0 failures. Refuted controls:
  a wrong row-5 label (22 146 nesting failures at h = 11) and a 2-subset centre (277 200 RG + JV violations at h = 12).
- **Referee's overclaim, corrected.** An earlier note quoted a larger exponent for E1 with the pre-pass. That figure
  needs the unproved batching recurrence (the open note above). Under the proved Thm 2.6′ the value is 4.37·10⁻¹¹.

## What remains open

1. **A human referee** of `proofs/PROOF.md`, and of the preprint's §2, whose architecture it reuses. Until then: preprint-stage; checked by AI agents only, not human-refereed; asymptotic only.
2. **The RAM-model statement.** It needs Lemma 2.5 with radix-3^m digits: [arg], not claimed.
3. **Feasibility.** Every proved crossover is far beyond feasible k. The word length enters only as ln(w), so shortening
   the word cannot help.
4. **The true exponent of L_{F₂}(M_k)** remains open. This only shows θ′ < 1.
5. **The whole-residual batching recurrence** (PROOF.md §11), a conjecture.

## Files (scripts and logs in `certificates/`)

| File | What it is |
|---|---|
| `proofs/PROOF.md` | The written proof, tagged step by step (not in `certificates/`). |
| `x1_e2e_rep.c` | Symmetry-reduced end-to-end check (build with `cc -O2 -DH=…`), plus logs `run_rep_h{6,7,8,9,10}_bad0.txt`, `run_rep_h7_bad{1,2}.txt` and `run_rep_h6_bad0.txt`. |
| `run_xref_h6_bad{0,2}.txt` | Logs of the reproduced `m5_xref_e2e.c` run at h = 6. |
| `x1_real_arrays.py` | Real-array test (needs numpy; every other script is stdlib-only), plus logs `run_real_A_f2*.txt` and `run_real_B*.txt`. Mode 4 runs the pre-pass and mode 5 its one-sided control. Config B is re-run in about 1 s. |
| `x1_exponent_count.py` | Count at h = 79..92 re-derived from Lemma 5.1, checked against brute force at h = 6..10, plus log `run_exponent_count.txt`. |
| `x1_word_check.py` | Independent check of the S⊗S word, plus log `run_word_check.txt`. |
| `x1_prepass_check.py` | Lemma 6.1 on the Fourier side, 42 lines, with the one-sided control; log `run_prepass_check.txt`. |
| `x1_e1_check.py` | Lemma 10.1 and one E1 invocation at h = 11, 12, with two controls; log `run_e1_check.txt`. |
| `x1_e1_rep.c` | E1 full-network check (Theorem 2) at h = 8–11, plus logs `run_e1_rep_h{8,9,10,11}_bad0.txt`, `run_e1_rep_h11_bad1.txt`, `run_e1_rep_h12_bad2.txt`. |
| `x1_theorems.py` | The three rows: closed forms vs the cell walk, sign thresholds, best h, 1 − θ′, crossovers; log `run_theorems.txt`. |

Every run used nice -n 15, one core, at most 330 MB and at most 220 s (alarm 600).
