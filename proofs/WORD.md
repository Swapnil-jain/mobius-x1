# WORD: explicit transfer word for X1, and an adversarial referee of X1's transfer steps 3–4

Written 2026-10-11 as part of X1.

**Scripts:** in `certificates/`; run them from there. Every run used nice -n 15 and alarm 600 on one core.

| Script | What it does | Time | Memory |
|---|---|---|---|
| `m6_word_search.py` | Exhaustive search at L ≤ 3, random sampling at L ≥ 4 | 7 s | 16 MB |
| `m6_word_L4.c` | Exhaustive L = 4 (11.4M words) | 0.8 s | 1.3 MB |
| `m6_word_L5.c` | Exhaustive L = 5 (2.56e9 words) | 32 s | 1.3 MB |
| `m6_word_verify.py` | Builds and exactly verifies the words; `-v` prints every matrix | 0.7 s | – |
| `m6_word_cross.py` | Checks C' XOR-count programs; recomputes ε' and the crossover | <1 s | – |

**Conventions.**
- F₁₆ = F₂[x]/(x⁴+x+1). Elements are written as integers, with bit i the coefficient of xⁱ.
- ω = x⁵ = 6 and ω² = 7.
- C' = ωI + ω²J₃ = [[1,7,7],[7,1,7],[7,7,1]].
- **Only the forward C' is used.** No inverses and no Frob(C') appear anywhere.

---

## 1. An explicit positive word, with w = 12 slots at width 4 [proof by exact computation]

### Algebra that makes the search small [proof]

- ω²C' = I + ω·jjᵀ, where j = (1,1,1) and jᵀj = 3 = 1. So, up to a scalar, C' is a **homology**: it fixes the plane Σx_i = 0 and
  scales j by ω².
- Pj = j for every permutation P, so **permutations commute with C'**. Scalars commute too.
- Hence every positive word M₀C'M₁C'⋯C'M_L equals, up to outer monomials, C'D₁C'D₂⋯D_{L−1}C' with D_i diagonal and normalised to
  d₁ = 1. That gives 225^{L−1} words, so **searching all lengths L ≤ 5 is exhaustive.**
- Test used: an invertible 3×3 matrix is monomial·(I+aE_ij)·monomial **iff it has exactly 4 nonzeros**. (A permutation support plus
  one extra entry; the determinant is a single term.)
- With 5 nonzeros it is a monomial times one of three things:
  - **A:** a row-type transvection I + e_c(b·e_a + d·e_e)ᵀ;
  - **B:** a column-type transvection, the transpose of A;
  - **C:** a 2×2 block ⊕ 1.

### Exhaustive histograms of nnz(C'D₁⋯C')

| L (C' factors) | Words | nnz = 4 (elementary) | nnz = 5 |
|---|---|---|---|
| 2 | 225 | 0 | 0 |
| 3 | 50 625 | 0 | 0 |
| 4 | 11 390 625 | **0** | 22 356 (A 6804, B 6804, C 8748) |
| 5 | 2.56·10⁹ | **58 320** | 2 875 176 |

**Consequences [proof by exhaustion]:**
- The shortest positive word for **S⊕1** (width 3) has exactly **5** C'-slots.
- The shortest positive word for a non-elementary type-A or type-B transvection has exactly **4**.
- At L = 2, the only products with zeros have 3 nonzeros (monomial, e.g. d = (ω²,1,ω²)) or 6. This matches the order-648 F₄ obstruction.

### Explicit S⊕1 at width 3 (w₃ = 5)

```
S⊕1 = M0 · C' D1 C' D2 C' D3 C' D4 C' · M1
D1=(1,1,2) D2=(1,1,14) D3=(1,4,11) D4=(1,14,3)
M0=[[0,2,0],[0,0,5],[4,0,0]]   M1=[[0,0,1],[1,0,0],[0,5,0]]
```

### Explicit S⊗S at width 4 (w = 12)

Coordinates are 00, 01, 10, 11 → 0, 1, 2, 3.

**Factorisation [proof, hand + script].** Transvections with the same centre (or the same axis form) commute and add, so

  S⊗S = T₁·T₂ₐ·T₂ᵦ, where
  - T₁ = I + (e₀₁+e₁₀)e₀₀ᵀ;
  - T₂ₐ = I + e₁₁(e₀₀+λe₁₀)ᵀ;
  - T₂ᵦ = I + e₁₁(e₀₁+(1+λ)e₁₀)ᵀ;
  - λ = 2 (any λ ∉ {0,1} works).

Each factor lives on 3 coordinates:
- T₁ is a type-B transvection on {0,1,2};
- T₂ₐ and T₂ᵦ are type-A transvections on {0,2,3} and {1,2,3}.

Each factor is therefore one 4-slot word. The type-A word below is reversed for type B, because C' and the D_i are symmetric.

```
type-A core:  C' D1 C' D2 C' D3 C',  D = (1,2,7),(1,5,6),(1,5,5)  -> [[0,5,0],[8,0,0],[8,13,10]]
T1  on (0,1,2): M0=[[0,0,12],[0,4,0],[15,0,0]] · C'(1,5,5)C'(1,5,6)C'(1,2,7)C' · M1=[[0,6,0],[0,0,1],[1,0,0]]  = [[1,0,0],[1,1,0],[1,0,1]]
T2a on (0,2,3): M0=[[0,15,0],[2,0,0],[0,0,15]] · C'(1,2,7)C'(1,5,6)C'(1,5,5)C' · M1=diag(1,12,10)            = [[1,0,0],[0,1,0],[1,2,1]]
T2b on (1,2,3): M0=[[0,15,0],[13,0,0],[0,0,15]] · C'(1,2,7)C'(1,5,6)C'(1,5,5)C' · M1=diag(1,10,10)           = [[1,0,0],[0,1,0],[1,3,1]]
```

- Each 3×3 piece is embedded as identity on the 4th coordinate.
- A C' on coordinates {0,2,3} or {1,2,3} is a permutation conjugate Π(C'⊕1)Π⁻¹, which was checked.
- `m6_word_verify.py -v` prints all 27 4×4 slot matrices: 12 C' slots and 15 monomials, which merge to 13.
- Their product was **checked to equal S⊗S exactly over F₁₆** (all entries 0/1).

**What this closes.**
- **Ostrom–Wagner and the 2-transitivity computation are no longer needed** for X1.
- The lower bound for any route through 3-coordinate transvections is 4 per transvection, and S⊗S−I has rank 2. So at least 8
  slots are needed via this route [arg].
- **This does not matter:** w enters the crossover only through ln w (§3).

---

## 2. Adversarial referee of transfer steps 3–4

| Item | Verdict | Reason |
|---|---|---|
| (a1) Mixed product: M_{2t} = (S⊗S)^{⊗t} = Π_i W_i^{⊗t} | **HOLDS** [proof] | Tensor is associative, so S^{⊗2t} with pairs grouped is (S⊗S)^{⊗t} exactly. (AB)^{⊗t} = A^{⊗t}B^{⊗t}. Π^{⊗t} of a permutation is a permutation, which is free. M^{⊗t} of a monomial is monomial. |
| (a2) Sectors decouple | **HOLDS** [proof] | For each pattern R ⊆ [t], the span V_R of e_{i₁…i_t} (i_j ∈ {0,1,2} for j ∈ R, i_j = 3 otherwise) is invariant under (C'⊕1)^{⊗t}, which acts on it as C'^{⊗\|R\|}. The V_R are coordinate subspaces with disjoint supports covering all 4^t coordinates. So the operator is block-diagonal in the standard basis, with no cross terms, and blocks with different r share nothing. |
| (a3) The gadget bound applies to each sector with F₁₆ data | **HOLDS** [proof] | The gadget is an F₄-linear circuit (constants: powers of ω, the F₂ maps R/G/J, the correction kernels). A linear circuit with coefficients in K computing A computes A on any K-vector space, in particular F₁₆^n. Better still, F₁₆ = F₄ ⊕ F₄β, so the F₄ circuit runs twice, once per component. No step uses that the data field is exactly F₄. The bound O(3^r(r+1)^{θ'}) is uniform in r (Yates on C' below K, constant A), so it holds for every sector size, including r = 0 (no gates). |
| (b) Jensen | **HOLDS** [proof] | Σ_r C(t,r)3^r·A(r+1)^{θ'} = 4^t·A·E[(R+1)^{θ'}], R ~ Bin(t,3/4), and x ↦ (x+1)^{θ'} is concave for 0 < θ' < 1. So this is ≤ 4^t·A·(3t/4+1)^{θ'}. It needs only cost(C'^{⊗r}) ≤ A·3^r(r+1)^{θ'} for all r, which is (a3). For the explicit constant (§3) Jensen is not even needed: R concentrates at 3t/4. |
| (c1) "≤ 28 XORs per F₁₆ gate" | **HOLDS** [proof] | Multiplication by a fixed α ∈ F₁₆ is a 4×4 F₂ matrix, ≤ 3 XORs per output bit, so ≤ 12. αu+βv ≤ 12+12+4 = 28. **Tighter and more natural:** the slots are F₄-circuits, so on F₁₆ data an F₄ gate costs 2×(1+1+2) = 8 XORs (multiplying by ω or ω² is 1 XOR on F₄ = F₂²). C' on F₁₆³ costs 28 XORs total. The 14-XOR F₄ program y_i = ωx_i + ω²s was checked on all 64 inputs. |
| (c2) Cost of the F₁₆ monomial slots | **HOLDS** [proof] | M_i^{⊗t} is a permutation (free) times a diagonal. Each of the 4^t entries is multiplied by one fixed F₁₆ constant, ≤ 12 XORs. There are ≤ 13 merged monomial slots, so ≤ 156N XORs = O(N). Constants could also be folded into adjacent gates. |
| (d) F₂ in, F₂ out, valid F₂ circuit | **HOLDS** [proof] | Replace every F₁₆ wire by 4 F₂ wires and every gate by its XOR block. The result is an F₂-linear circuit computing the F₂-restriction of the F₁₆-linear map M_k on F₁₆^N. Because M_k has 0/1 entries, that map is M_k ⊗ I₄ in the basis {1,x,x²,x³}. Feed x as (x,0,0,0) and read component 0. Constant-zero inputs only delete gates. Fan-in 2 is preserved, and cancellation is allowed in the model. |
| (e) Odd k as a corner | **HOLDS** [proof] | M_{k+1} = S⊗M_k = [[M_k,0],[M_k,M_k]]. Input (x,0) gives (M_k x, M_k x). Cost is ≤ L(M_{2⌈k/2⌉}) = O(2N(log 2N)^{θ'}). |
| Hidden k-dependence | **none found** [arg] | w = 12 is fixed. Monomial scalings are O(N). The gadget's pointwise work enters with weight A/(m·K·c) per level, which is negligible (the same accounting as PROOF.md Thm 2.6′). |

**Net [arg, with X1's gadget recursion still the only [arg] input]:**

  L_{F₂}(M_k) ≤ 12·Σ_r C(t,r)·L_{F₂}(C'^{⊗r} on F₁₆) + O(N) = O(N(log N)^{θ'}), with an explicit slot count.

---

## 3. Explicit end-to-end crossover (`m6_word_cross.py`)

**Constants.**
- ε' = Δ'/(W*·m), with h = 92, v = C(92,4) = 2 794 155, c = 4279, m = h³ = 778 688, Δ' = v²(v−6ch) = 3 373 902 208 276 911 675, and
  W* = 3^55. This gives **ε' = 2.4837·10⁻¹⁴**, matching PROOF.md Thm 2.6′.

**Cost per entry (N = 4^t, k = 2t).**
- Yates: t XORs.
- Pipeline: w·(c_{C'}/3)·E[R]·(1−ε')^d = (w·c_{C'}/4)·t·(1−ε')^d, where:
  - d is the number of gadget levels, with r ≈ K·m^d and K = 56m;
  - c_{C'} is the number of XORs for one C' on F₁₆³.

**Result.** The pipeline beats Yates iff d > ln(w·c_{C'}/4)/ε', and then log₁₀ k ≈ d·log₁₀ m.

| Descent model | w·c_{C'}/4 | Levels d | **log₁₀ k at crossover** |
|---|---|---|---|
| F₄-componentwise (c_{C'} = 28 XORs) | 84 | 1.784·10¹⁴ | **1.051·10¹⁵** |
| 28 XORs per F₁₆ gate, 5 gates per C' (c_{C'} = 140) | 420 | 2.432·10¹⁴ | **1.433·10¹⁵** |

- **This replaces "log₁₀ k ≈ 10^15 for any plausible word length" with log₁₀ k ≈ 1.05·10¹⁵ (explicit word, w = 12).**
- **The word is irrelevant to feasibility.** Even w·c_{C'}/4 = 2 would still need about 2.8·10¹³ levels. The crossover is set by
  1/ε' alone.

---

## Closed routes

| Idea | Verdict |
|---|---|
| Elementary transvection with ≤ 4 C' slots (width 3) | **Impossible [proof by exhaustion, L ≤ 4]**; 5 is minimal. |
| H·D·H with zeros other than the monomial case | At most a 6-nonzero symmetric pattern. X·E·X of that pattern has zeros only on the diagonal, so it is a dead end [proof, hand]. |
| Shorter word ⇒ feasible crossover | **No.** The crossover depends on the word only through ln(w·c_{C'}) and is set by ε' [proof from the cost formula]. |
| Ostrom–Wagner / the 2-transitivity route | Superseded by the explicit word; it is no longer needed. |

## Summary
1. The transfer word is found and exactly verified. S⊕1 = M₀·C'D₁C'D₂C'D₃C'D₄C'·M₁ (5 slots, minimal by exhaustion). S⊗S is a product of
   **w = 12** slots (C'⊕1), as three 4-slot transvection words, with F₁₆ monomials. Only forward C' is used.
2. With the explicit word, Ostrom–Wagner and 2-transitivity drop out of X1. The only [arg] left is the gadget recursion itself.
3. Steps 3–4 refereed: mixed product, sector decoupling, the gadget on F₁₆ data, Jensen, the 28-XOR figure (8 per F₄ gate is
   tighter), O(N) monomial slots, the subfield read-off, and odd k all **HOLD**. No GAP, no hidden k-factor.
4. Explicit crossover: ε' = 2.4837e−14 gives log₁₀ k ≈ **1.05·10¹⁵**, or 1.43·10¹⁵ under the crude 28-XOR/gate descent.
5. The word length is irrelevant to feasibility (it enters as ln w).
6. These crossovers are for Theorem 1. Theorems 1′ and 2 use the same word with their own ε and m (PROOF.md §8).
