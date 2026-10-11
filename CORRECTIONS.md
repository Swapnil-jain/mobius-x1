# Corrections

Dated corrections to the proofs, the checks and their descriptions. None of them changes Theorem 1
(1 − θ′ = 1.8309·10⁻¹⁵).

## 2026-10-11 (the pre-pass and E1)

- **Overclaimed exponent, corrected (found by the pre-pass referee).** An earlier internal note quoted larger
  exponents for the E1 gadget and for the 4-subset gadget with the pre-pass. Both figures assume a "whole-residual
  batching" recurrence, with one C′^{⊗ρf} call per residual and no padding. That recurrence is not proved. Under the proved recursion (Thm 2.6′, padded) the values are **4.37·10⁻¹¹ (Theorem 2)** and
  **4.22·10⁻¹³ (Theorem 1′)**. The batching value now appears only as a conjecture (`proofs/PROOF.md` §11).
- **Placement of the pre-pass.** It was first credited to the preprint's Lemma 2.5, which X1 does not use. It is now a
  proved step in Prop 2.4′, the exceptional route, with the counts of §5 (s′_μ, Δ_μ), as Lemma 6.1.
- **Scope of the pre-pass.** "Every odd label prime" was a sketch. Lemma 6.1 is proved for p = 3 only, which is all
  that is used. The cell-decomposition picture that came with the sketch is not needed and is not claimed.
- **An earlier closure was wrong.** An internal note concluded that the correction kernel is forced for odd label
  primes (μ = 1). That holds only for output-side (one-sided) adapters. A two-sided pre-pass removes it. The gotcha
  is now written at Lemma 6.1, and `docs/CLOSED_IDEAS.md` lists only the one-sided version as closed.
- **E1's side-wire convention, now stated.** E1 places side wires only on the pairs where J ≠ 0, the ordered pairs with
  |S∩T| = 3, which gives 35·C(h−7, 4) per entry. This is valid because J = C(n,3) mod 2 = 0 at |S∩T| ∈ {0, 6}, and
  Definition 1.1 now allows any side-wire set containing the support of J.
- **E1 crossover.** An earlier note quoted a crossover computed from the unproved batching figure, under a different
  convention. With `proofs/PROOF.md` §8's
  formula and the proved exponent, it is 6.9·10⁹ to 1.4·10¹¹ for c₀ between 2 and 10⁶ (4.4·10¹⁰ at c₀ = 84).
- **A vacuous control.** A 2-subset centre on 7-subsets of [11] passes, because two 7-subsets of [11] always meet in at
  least 3 points, so the non-neighbour size 2 never occurs. `x1_e1_check.py` runs that control at h = 12, where it
  fails (1 214 failures).
- **The end-to-end run behind the pre-pass.** It was not reproducible from the referee's directory, because it imported
  missing scripts. It is replaced by `x1_prepass_check.py` (42 lines on the Fourier side) and by mode 4 of
  `x1_real_arrays.py` (configs A and B, every role correct). `x1_real_arrays.py` now prints the predicted count as
  Wm − μN₀ + 2Σ c h_j, with μ shown.

## 2026-10-11 (the two referees of Theorem 1)

- Paths are self-contained, and the word scripts and the h = 6 end-to-end check are included.
- The brute-force comparison is extended from h = 6 to h = 6–10, parsed from the logs.
- The h = 79–92 count is labelled as a re-derivation from Lemma 5.1, not independent evidence.
- The numpy dependency is stated.
- Notes added: J = −RG in characteristic 2; z ≠ 0 in Lemma 3.4; the loose 28-versus-12 XOR charge.
- "Modulo the preprint" was replaced: no statement of the preprint is used as a hypothesis.
