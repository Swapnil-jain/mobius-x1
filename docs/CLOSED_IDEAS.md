# Closed ideas

This file lists approaches to a faster XOR circuit for the GF(2) Möbius transform M_k = S^{⊗k}, S = [[1,0],[1,1]], that
we tried and found do not work. Each row gives its reason. We list them so that other researchers, and automated
searches, do not spend time on these routes again.

**Contributing.** Please check this list before starting on a route, so effort is not duplicated. If you find a mistake
in a closure, or an idea that escapes a stated hypothesis, please send the argument. Corrections are welcome and will
be credited.

**Scope.** A closure holds only inside its stated model or hypotheses. Nothing here is a lower bound for L_{F₂}(M_k) in
general. An idea that breaks a stated hypothesis is not covered by its row.

**Status labels.**
- [proof]: a complete argument.
- [computation]: an exhaustive or exact computer check, at the stated sizes.
- [arg]: a short argument, convincing but not written as a full proof.

All rows are our own work unless a source is named.

**Model.** Fan-in-2 linear circuits over F₂ that may cancel. L(A) is the least number of XOR gates computing x ↦ Ax.
Yates costs (1/2)·N log₂ N = k·2^{k−1}.

## 1. Direct constructions over F₂

| Idea | Why it fails | Status |
|---|---|---|
| Low-rank plus sparse Kronecker lift (the Alman–Rao idea, transplanted to GF(2)) | Write M_t = L + E with rank(L) = r. The columns of M_t are independent, so E has at most r zero columns. The lift (L+E) ⊗ M_{k−t} then needs at least r + nzc(E) ≥ 2^t sub-transforms, the same as Yates. Alman–Rao's gain in characteristic ≠ 2 does not transfer. | [proof] for the leading term |
| Unequal or split-radix tensor recursions (M_a ⊗ I)(I ⊗ M_b) | Every split costs Yates exactly with optimal blocks, given L(M₃) = 12. | [proof] |
| Border rank, degeneration over GF(2)[ε] | GF(2)[ε] unrolls coefficient by coefficient into an XOR circuit that is no smaller, and interpolation needs h + 1 field points. | [proof sketch] |
| F₄ diagonalisation of S | S = W·J with W multiplication by ω in F₄. The Galois-descent change of basis costs at least 1 XOR per 4 bits per level, since no permutation basis exists. The total is at least Yates. | [arg]; [proof] at k = 2 |
| Catalytic or "dirty" registers | Fresh memory is free in circuits. Restoring scratch values only adds gates. | [proof] |
| Lookup tables (Alman, arXiv 2211.04643) | Needs data-indexed addressing, so it is outside the linear-circuit model. | model |
| Additive FFTs (Cantor, Lin–Chung–Han, Gao–Mateer, Bernstein–Chou) | The binary Möbius transform is the case with every twiddle equal to 1. A change of basis only adds cost. | [arg] |
| Taylor shift by 1 in characteristic 2 | (t+1)^{2^j} = t^{2^j} + 1, so divide and conquer rebuilds Yates. The convolution form needs factorials. | [arg] |
| Fast real Pascal-matrix algorithms | Their factorial scalings vanish mod 2. | [arg] |
| Cellular-automaton (rules 60/102) jump identities | (I + E)^{2^j} = I + E^{2^j} rebuilds Yates. | [proof] |
| Algebraic products from the relations M² = I, (MJ)³ = I, MJM = Mᵀ, JM = MMᵀ | These generate Kronecker powers of a 6-element group of 2×2 relations. The result is either Yates regrouped or circular. | [proof] |
| "All-but-one" gadgets with every input live | Distinct rows of M_k differ in at least 2^{max(\|A\|,\|B\|)−1} entries, so there are no cheap pieces. No all-but-one gadget with n ≥ 3 exists from subcube pieces. | [proof] |
| Complement, superset and inclusion–exclusion identities | No gain at any k in circuits whose every value is a subcube sum. | [proof] (all-subcube circuits) |
| Subcube plus equal-diagonal circuits | No circuit below Yates at k = 4. | [computation] |
| Truncate-then-pad hybrids (BHKK rows plus Yates rows), and splices reusing Yates' internal signals | Hybrids lose (239 vs 192 at k = 6, 553 vs 448 at k = 7). One coordinate order gives only a chain of k + 1 superset sums, and the corner needs sums that are never subcube sums. | [computation] k ≤ 8; [proof] for the splice |
| Gray-code fast exhaustive search (Bouillaguet et al., CHES 2010) as a sub-Yates circuit | The updates alone cost Yates. | [computation] k ≤ 7 |
| Selezneva's k = 3 technique, extended to k = 4 or beyond | It is a linear recursion (27 at k = 4) plus a +1 equality case. | [arg] |
| Sergeev's 3N method, pushed beyond 3N | The method is linear by construction. | [arg] |

## 2. Lower-bound routes

| Idea | Why it fails | Status |
|---|---|---|
| An Ω(N log N) lower bound from a tensor-additive potential p with p(S) = 1 and subadditivity | Theorem 1 gives L(M_k) = o(N log N), so no such potential can force kN/2. | [arg], given Theorem 1 |
| Row-weight potential Σ log₂ w(row) | Fails on the prefix-sum matrix (log₂ n! against n − 1). | [proof] |
| Row-entropy potentials and their subadditive hulls, as kN/4 potentials | Row entropy fails subadditivity, and the hulls fail tensor additivity (H(M₃) ≤ 11.17). | [proof by counterexample] |
| The in-place CNOT count c₀ (transvection word length) as a potential | It fails the corner law: some K ∈ GL₇(F₂) has c₀(K) ≤ 6, but a corner of K has c₀ = 7. | [proof] |
| Plain Morgenstern bound, log \|det\| over integer lifts | M_k is unitriangular, so the bound is 0. | [proof] |
| Morgenstern over lifts, as a potential | It is 0 on S, and subadditivity fails through M₃ = (S⊗I₄)(I₂⊗M₂). | [proof] |
| 2-adic or residue-field lifting as a construction (Z₂, Z₂[i], Z/2^e, ramified extensions) | It is an exact reformulation (L_{F₂} = the least number of unit–unit gates). Every known characteristic-0 route forces a 1/2. | [proof] |
| 2×2 integer lifts B ≡ S mod 2 with cheap B^{⊗k} | Any sub-Yates unit–unit circuit would itself be a sub-Yates F₂ circuit. | [proof] |

## 3. The frame-and-label gadget (X1)

| Idea | Why it fails | Status |
|---|---|---|
| **Barrier: no frame/label gadget of the preprint's kind, transferred through F_{2^r}, beats Yates at k ≤ 64** | Per level, ε ≤ μ/(2m). Even allowing whole-residual batching, the per-level saving is a ≤ 0.032·μ, so a ≤ 0.064 at μ = 2. With characteristic-2 data the label prime is odd, so the kernel is a p × p operator over F_{2^r}, never S itself. A word plus descent then costs a factor ρ ≳ 8 per level for p = 3. Beating Yates needs (1 − a)^d·ρ < 1 with d ≤ log_m k levels, so at k ≤ 64 (d ≤ 2) it needs a ≥ 0.167, even at ρ = 2. | [arg]. Scope: the preprint's three tensor stages, with labels as gate-common subspaces and cost = residual dimension. |
| Tuning X1 toward feasible k: label primes, label families, centres, padding, frame reuse, a shorter word | Ruled out by the barrier above. The word length enters only as ln w. | [arg] |
| A shorter word for S⊗S, for a feasible crossover | The crossover depends on the word only through ln(w·c_{C′}). It is set by ε. | [proof from the cost formula] |
| Label primes p = 5, 7, 11, 13 and up; subset sizes 1, 2, 5 and 8 to 16; signed labels; thinned 7-subset families | Each is worse than p = 3 with 7-subsets, or admits no gadget. | [computation] |
| F₂ labels with any characteristic-2 data (F₄, F_{2^r}, Z/2^e, Z/4 with carries) | Killed by a Schur law and a Frobenius law; carries need about k/2 bits of precision. | [proof] |
| A frame gadget with the kernel S itself, without F₁₆ | It needs p = 2 labels, which characteristic-2 data rules out (previous row). | [arg] |
| Frame reuse across levels, so that ε grows like Δ/W | The saving is per directional step, m steps per array. | [arg] |
| Two-call factorisation of S through C′ over F₉ | Impossible. | [proof] |
| An X1 transfer using only F₄ (any width) | Impossible for exact words: the words stay in a unitary group. | [proof] |
| An elementary transvection with at most 4 C′ slots (width 3) | Impossible by exhaustion at L ≤ 4. 5 slots are minimal. | [computation] |
| **An output-side (one-sided) monomial adapter that removes the correction kernel** | R_u·C′^{−⊗m} is never monomial (0 of 42 lines, m ≤ 4, f ≤ 2; 18 of 18 Y_d fail in a real network). Note: a **two-sided** pre-pass does remove the kernel (Lemma 6.1). An earlier closure that called the kernel "forced" was wrong (CORRECTIONS.md). | [proof + computation], one-sided only |
| Ostrom–Wagner as the citation for the generation step | Its hypothesis (antiflag transitivity) is not met. It is moot: the 12-slot word is explicit. | [proof] |
| A 2-subset centre, or X1's \|P\| ≤ 2 centre, on 7-subset labels | C(2,2) and 1 + 4 + C(4,2) are odd at non-neighbour sizes, so RG + JV ≠ I. | [proof] (Lean `ControlsPrepass`) |

## 4. Literature and repositories checked (nothing applicable)

| Source | Finding |
|---|---|
| Rebalancing and the asymptotic spectrum (Alman–Guan–Padaki; Alman–Li; Sergeev arXiv 2212.01776) | Depth 2 or bounded depth only. |
| Symmetric XOR-circuit lower bounds (arXiv 2302.05426) | Not applicable: Yates is not S_k-invariant. |
| Polar and Reed–Muller hardware "XOR savings" | Only systematic, pruned or time-multiplexed variants. No claim for the full transform. |
| Range searching (Chazelle; Larsen; Pătraşcu–Demaine; and others) | Semigroup only (where Yates is optimal), bounded-coefficient reals, or per-operation bounds. |
| Bitsliced and word-level ANF transforms | Word operations, or speed-ups that depend on the input. Not linear circuits. |
| Network-coding gap constructions as a circuit for M_k | All-but-one gadgets (closed above), or characteristic-3 local codes that cannot be self-orthogonal in characteristic 2. |
