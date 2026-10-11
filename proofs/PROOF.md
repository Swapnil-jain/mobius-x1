# X1: written proof of the flipped network (F₃ labels, F₄ data) and of the transfer to M_k over F₂

Preprint-stage. Agent-written, **not human-refereed**. Three statements are proved here, all under the same recursion
(Thm 2.6′: one directional step per kernel, roles padded to a power of 3):

| Statement | Gadget | Exceptional route | 1 − θ′ | Status |
|---|---|---|---|---|
| **Theorem 1** | 4-subset labels, Lucas centre \|P\| ≤ 2 (§1) | one correction kernel (μ = 1) | 1.8309·10⁻¹⁵ (h = 92) | refereed twice by AI agents |
| **Theorem 1′** | the same | two-sided monomial pre-pass (μ = 2, Lemma 6.1) | 4.2213·10⁻¹³ (h = 51) | pre-pass refereed once by an AI agent |
| **Theorem 2** | E1: 7-subset labels, centre \|P\| = 3 (§10) | pre-pass (μ = 2) | 4.3713·10⁻¹¹ (h = 23) | refereed once by an AI agent; no full 7-set network run |

A faster recursion ("whole-residual batching") would give more; it is **not proved** and appears only as a conjecture
in §11.

Every step carries one tag:

- **[proof]**: a complete argument is written here.
- **[arg]**: an argument that is convincing but leaves routine details to the reader.
- **[cite]**: taken from a source without re-proving it.

"Checked" names the script in `certificates/` that machine-checks the step; script and log names below are relative to that directory. They are listed in `docs/RESULT.md`. The Lean modules are in `lean/`.

The source is the openai/math preprint "An explicit power saving for the exact DFT", `sections/network.tex`, §2 (Lemmas 2.1–2.5,
Prop 2.4, Thm 2.6). It was read as data from GitHub. Its proof is written over ℂ with the kernel C = [[a,b],[b,a]], a = (1+i)/2.
Nothing below uses the preprint's statements as hypotheses. The preprint supplies the *architecture*: the eight-row schedule,
the three stages, and the shape of the label table. Every step is re-proved here in the flipped setting. §8 lists exactly what
is re-proved and what is still cited.

---

## 0. Conventions

- **Fields.** F₄ = F₂(ω) with ω² + ω + 1 = 0. The data live in F₄ (later F₁₆ ⊇ F₄). The labels live in F₃. Since ω³ = 1, the
  power ω^s is well defined for s ∈ F₃.
- **Two identities used throughout [proof].** In F₄ we have 1 + ω² = ω and 1 + ω = ω². Hence 1 + ω^{2n} = ω^n for n ∈ {1, 2}.
- **Arrays.** An *array* on the address space A = F₃^m is a function g : A → F₄. Translation is (R_z g)(x) = g(x + z).
- **Fourier transform.** F = (ω^{x·y})_{x,y∈A}, using the standard dot product. Then F·F̄ = 3^m·I = I, because for a ≠ 0 the sum
  Σ_y ω^{a·y} = 3^{m−1}(1 + ω + ω²) = 0, and 3 = 1 in characteristic 2. So F⁻¹ = F̄ = (ω^{−x·y}).
- **Characters to translations [proof].** For z ∈ A put χ_z(y) = ω^{z·y} and let D_φ denote the diagonal matrix of φ. Then
  (F D_{χ_z} F⁻¹)_{x,x'} = Σ_y ω^{(x + z − x')·y} = [x' = x + z]. Hence **F D_{χ_z} F⁻¹ = R_z**.
- **The kernel.** C' = ωI + ω²J₃ = [[1,ω²,ω²],[ω²,1,ω²],[ω²,ω²,1]]. Frob(C') denotes the entrywise square, ω²I + ωJ₃.
- **Quadratic form.** Q(y) = y·y ∈ F₃. A subspace U ⊆ A is *nondegenerate* if its Gram form has zero radical. In that case
  A = U ⊕ U^⊥, and P_U denotes the projection onto U along U^⊥.
- **Cost model.** We use linear circuits over a field K. Each gate computes αu + βv with α, β ∈ K. Address permutations are
  relabelings of wires, so they cost 0. L_K(A) is the least number of gates that computes x ↦ Ax.

---

## 1. Admissible data and the network

**Definition 1.1 (admissible data).** For j = 1, 2, 3 take:
- a factor space D_j = F₃^{h_j};
- a family 𝒯_j = (t_1, …, t_{v_j}) of vectors with t·t = 1 (repetitions and t, −t are allowed);
- an *F₂-gadget* (R_j, G_j, J_j). Call distinct indices S, T *neighbours* if t_S·t_T = 0. The gadget is a v_j × c_j matrix R,
  a c_j × v_j matrix G and a v_j × v_j matrix J over F₂, with J supported on ordered neighbour pairs, such that
  **RG + JV = I**, where (Vx)_{ST} = x_T on ordered neighbour pairs. Equivalently: (RG)_{SS} = 1, (RG)_{ST} = 0 for distinct
  non-neighbours, and J_{ST} = (RG)_{ST} for neighbours.
- a *side-wire set* 𝒩_j: any set of ordered neighbour pairs that contains the support of J_j. V is read on 𝒩_j only,
  (Vx)_{ST} = x_T for (S, T) ∈ 𝒩_j. Since J vanishes off 𝒩_j, JV is the same map for every such choice. The 4-subset
  instance takes all ordered neighbour pairs (its J is 1 on all of them). E1 (§10) takes exactly the support of J.
  *Note (characteristic 2).* The identity is RG + JV = I, so on neighbour pairs J = −RG; the data field has characteristic 2,
  so −1 = 1 and this is written J = RG. Lemma 1.2 uses 2 = 0 in the data field (F₄) only here, and nowhere uses 1/2.

Put m = h₁h₂h₃ and A = D₁ ⊗ D₂ ⊗ D₃ = F₃^m, with the tensor dot product (it is the standard dot product on F₃^m).

**The genuine instance.**
- h_j = h for every j.
- 𝒯 is the set of indicators of the 4-subsets of [h]. Their norm is 4 ≡ 1, and S, T are neighbours iff |S∩T| ∈ {0, 3}.
- The **Lucas centre** has one wire c_P for each P ⊆ [h] with |P| ≤ 2, so c = 1 + h + C(h,2). It uses
  (Gx)_P = Σ_{T⊇P} x_T, (Rc)_S = Σ_{P⊆S} c_P and J = RG restricted to neighbour pairs.

**Lemma 1.2 (Lucas centre) [proof].**
- (RG)_{ST} = #{P ⊆ S∩T : |P| ≤ 2} = 1 + n + C(n,2) with n = |S∩T|.
- Mod 2 this is 1, 0, 0, 1, 1 for n = 0, 1, 2, 3, 4.
- So RG = 1 on the diagonal (n = 4) and RG = 0 on non-neighbours (n ∈ {1, 2}). With J := RG on neighbours, RG + JV = I.

Checked: `x1_e2e_rep.c` [1a] at h = 6, 7, 8, 9, 10 (0 wrong entries). Negative control: with a centre of size ≤ 1, 630 entries
are wrong at h = 7.

**The network.** There are two banks of wires, X_d and Y_d, for d ∈ 𝒯₁ × 𝒯₂ × 𝒯₃, so N₀ = v₁v₂v₃.
- Stage j has one *invocation* for each choice of the two indices other than d_j. There are I_j = N₀/v_j invocations.
- Each invocation owns fresh auxiliary wires: one side wire A_{ST} per pair (S, T) ∈ 𝒩_j, and c_j centre wires.
- The physical wire count is W = 2N₀ + Σ_j I_j(v_j·d_j + c_j), where d_j is the number of pairs of 𝒩_j that start at one
  entry. When these counts are not constant, read v_j·d_j as |𝒩_j|.

**Schedule.** In stages 1 and 3 the logical source is x = X and the target is y = Y. Characteristic 2 removes all signs. The
eight rows of the forward invocation are:

| Row | Update | Wires touched (gate grouping) |
|---|---|---|
| 0 | y ← y + JA | one gate per target S with its side wires A_{S·} |
| 1 | y ← y + Rc | targets and centre |
| 2 | A ← A + Vx | one gate per source T with its side wires A_{·T} |
| 3 | c ← c + Gx | sources and centre |
| 4 | y ← y + Rc | targets and centre |
| 5 | y ← y + JA | per target S with A_{S·} |
| 6 | c ← c + Gx | sources and centre |
| 7 | A ← A + Vx | per source T with A_{·T} |

Stage 2 is the inverse forward invocation from Y to X. That means rows 7, 6, …, 0 with source Y and target X.

In every stage the physical touch order is the same: Y–side, Y–centre, X–side, X–centre, Y–centre, Y–side, X–centre, X–side.
We always index a side wire as A_{ST} with S the Y-entry and T the X-entry.

---

## 2. Lemma 2.1′ (scalar network over F₂)

**Lemma 2.1′.** For arbitrary initial auxiliary values:
- one forward invocation maps (x, y, A, c) ↦ (x, y + x, A, c);
- the three stages map (X_d, Y_d) ↦ (Y_d, X_d) for all d;
- every auxiliary value is restored.

**Proof [proof].**
- Rows 0–1 add JA + Rc to y.
- Rows 2–3 replace A, c by A + Vx, c + Gx.
- Rows 4–5 add R(c + Gx) + J(A + Vx).
- Rows 6–7 restore c and A.
- The net change of y is (JA + Rc) + (R(c + Gx) + J(A + Vx)) = (RG + JV)x = x, since 2(JA + Rc) = 0. Here JV is
  computed with side wires on 𝒩_j only, which is exact because J vanishes off 𝒩_j.

The inverse of y ↦ y + x is itself in characteristic 2, so stage 2 performs x ↦ x + y. Its reversed rows restore A and c in the
same way. The three stages then give (X, Y) → (X, X+Y) → (Y, X+Y) → (Y, X). The auxiliaries of each invocation are touched
only by that invocation, and each invocation restores them. ∎

Checked: `x1_e2e_rep.c` [1b] over **all** invocations with random F₄ values on every wire, at h = 6, 7, 8, 9, 10:
- h = 6: 0 / 6 750 bank failures;
- h = 8: 0 / 686 000 bank failures;
- h = 10: 0 / 18 522 000 bank failures;
- 0 auxiliaries are left unrestored in every case.

The negative control (Lucas centre of size ≤ 1) gives 64 541 failures at h = 7.

---

## 3. Lemma 2.2′ (frames and directional kernels)

**Frames.** For a nondegenerate U ⊆ A, put **Φ_U = F·D_{ω^{Q(P_U y)}}·F⁻¹**. Then Φ_0 = I, and all Φ_U commute, since they are
diagonal in the Fourier basis.

**Lemma 3.1 (one-variable identity) [proof].** For s ∈ F₃ and n ∈ {1, 2}: **ω^{n s²} = 1 + ω^{2n}(ω^s + ω^{−s})**.
- At s = 0 both sides equal 1, because ω⁰ + ω⁰ = 0.
- At s = ±1 the left side is ω^n. The right side is 1 + ω^{2n}(ω + ω²) = 1 + ω^{2n} = ω^n (§0).

Checked: `x1_real_arrays.py` self-checks.

**Definition.** For z ∈ A and n ∈ {1, 2}, put **K_{z,n} = F·D_{ω^{n(z·y)²}}·F⁻¹**.

**Lemma 3.2 [proof].** K_{z,n} = I + ω^{2n}(R_z + R_{−z}). Also K_{z,1}K_{z,2} = I, and K_{z,n}³ = I.
- Apply Lemma 3.1 pointwise with s = z·y, then use F D_{χ_{±z}} F⁻¹ = R_{±z}.
- The product K_{z,1}K_{z,2} is conjugate to D_{ω^{3(z·y)²}} = I.

**Lemma 3.3 (Φ of the full space) [proof].** Φ_A = C'^{⊗m}.
- Q(y) = Σ_i y_i², so D_{ω^{Q}} = ⊗_i D_{ω^{s²}}. Also F = F₁^{⊗m}.
- In one variable, F₁D_{ω^{s²}}F₁⁻¹ = K_{1,1} = I + ω²(R₁ + R₂) = I + ω²(J₃ − I) = (1 + ω²)I + ω²J₃ = C'.

**Lemma 2.2′ (edges).** Let U ⊆ V be nondegenerate and let E = V ∩ U^⊥ (the *residual*). Then:
- (a) V = U ⊥ E, and E is nondegenerate;
- (b) E has an orthogonal basis z₁, …, z_ρ with ρ = dim V − dim U and norms n_j = z_j·z_j ∈ {1, 2};
- (c) Φ_VΦ_U⁻¹ = Π_j K_{z_j, n_j} and Φ_UΦ_V⁻¹ = Π_j K_{z_j, −n_j}. These are exactly ρ directional kernels.
  *Note.* Each z_j is a basis vector of norm ±1, so z_j ≠ 0; this is the hypothesis z ≠ 0 of Lemma 3.4, which is only
  ever applied to these z_j.

**Proof [proof].**
- (a) Let v ∈ V. Then P_U v ∈ U ⊆ V, so v − P_U v ∈ V ∩ U^⊥. Hence V = U + E, and U ∩ E = 0 because U is nondegenerate.
  If e ∈ E is orthogonal to E, it is also orthogonal to U, hence to V. So e ∈ rad V = 0.
- (b) Characteristic 3 ≠ 2. If every vector of a nonzero space E had x·x = 0, polarisation 2x·y = (x+y)·(x+y) − x·x − y·y
  would make the form zero, contradicting nondegeneracy. So pick z₁ with z₁·z₁ ≠ 0. Then E = ⟨z₁⟩ ⊥ (E ∩ z₁^⊥), the second
  summand is nondegenerate by (a), and we recurse. The norms are nonzero elements of F₃, i.e. ±1. **No analogue of the
  preprint's h ≥ 7 condition arises** (that condition handles alternating forms in characteristic 2).
- (c) By (a), P_V = P_U + P_E, and P_E y = Σ_j n_j⁻¹(z_j·y)z_j with n_j⁻¹ = n_j. Orthogonality gives
  Q(P_V y) = Q(P_U y) + Σ_j n_j²·n_j(z_j·y)² = Q(P_U y) + Σ_j n_j(z_j·y)², because n_j² = 1. So
  D_{ω^{Q(P_V y) − Q(P_U y)}} = Π_j D_{ω^{n_j(z_j·y)²}}. Conjugate by F. The second formula is the inverse, by Lemma 3.2. ∎

**Lemma 3.4 (address change; inverse kernels are forward calls) [proof].** Let z ≠ 0, and let M ∈ GL_m(F₃) have M e₁ = z
(complete z to a basis). Put (Π_M g)(x) = g(Mx). Then:
- K_{z,n} = Π_M⁻¹·(K⁽¹⁾_n ⊗ I_{3^{m−1}})·Π_M, with K⁽¹⁾₁ = C' and K⁽¹⁾₂ = Frob(C') = C'² = C'⁻¹;
- **Frob(C') = D·P₂₃·C'·D** with D = diag(1, ω², ω²), where P₂₃ swaps the addresses 1 and 2 of F₃.

**Proof.**
- Π_M R_z Π_M⁻¹ = R_{M⁻¹z} = R_{e₁}. Insert this into Lemma 3.2.
- On one coordinate, K_{e₁,n} = I + ω^{2n}(J₃ − I). This is C' for n = 1 and ω²I + ωJ₃ for n = 2.
- The monomial identity is a direct 3 × 3 multiplication. C'D scales columns 1 and 2 by ω². P₂₃ swaps rows 1 and 2. D scales
  rows 1 and 2 by ω². The result is [[1,ω,ω],[ω,1,ω],[ω,ω,1]] = Frob(C'). ∎

Checked: `x1_real_arrays.py` (assertion) and `x1_word_check.py` (C'³ = I).

**f columns.** Index an array by f columns, each a copy of F₃^m, and use the frame Φ_U^{⊗f}. Lemma 2.2′ holds verbatim with
K_{z,n}^{⊗f}. After the address change M in every column, K_{z,n}^{⊗f} becomes (K⁽¹⁾_n)^{⊗f} on the f selected trits (one per
column), for every setting of the other trits. **That is one call of C'^{⊗f} on each fibre**, plus monomials when n = 2.

---

## 4. Telescoping (frames commute with the gates)

Give every gate a label, common to all wires it touches. Give every source and sink its own label. Along each wire, between
consecutive touches with labels U → V, insert the operator Φ_V^{⊗f}(Φ_U^{⊗f})⁻¹.

**Lemma 4.1 [proof].** The resulting linear map on the W arrays is diag_sinks(Φ^{⊗f})·𝒮·diag_sources(Φ^{⊗f})⁻¹, where 𝒮 is the
scalar network of Lemma 2.1′ applied pointwise in the address.

**Proof.** Run induction over the chronological sequence of edges and gates. The invariant is:
state = diag(Φ^{⊗f}_{current labels})·𝒮_{prefix}·diag(Φ^{⊗f}_{source labels})⁻¹·(initial values).
- An edge U → V on one wire multiplies that wire by Φ_V^{⊗f}(Φ_U^{⊗f})⁻¹. This just updates its current label.
- A gate acts as G ⊗ I_{addresses} on the wires it touches. Those wires all carry the gate's label L at that moment, and
  G ⊗ I commutes with I ⊗ Φ_L^{⊗f}. So the gate moves past the frames into 𝒮.
- The order of the edges along different wires is irrelevant. Each edge commutes with every operation on other wires. ∎

---

## 5. Lemma 2.3′ (labels, nesting, residuals, the dimension count)

At an invocation of stage j, write:
- E = D₁ ⊗ ⋯ ⊗ D_{j−1}, with dim e = h₁⋯h_{j−1} (E = F₃ when j = 1);
- Fu = D_{j+1} ⊗ ⋯ ⊗ D₃, with dim q;
- P = ⟨⊗_{l<j} t_{d_l}⟩ ⊆ E and B = P^⊥ ⊆ E;
- Q = ⟨⊗_{l>j} t_{d_l}⟩ ⊆ Fu and Q′ = Q^⊥ ⊆ Fu;
- t = t_{d_j} for an entry-specific gate.

**Gate labels.** Every gate label below is tensored with Q:

| Row | Wires | Label (⊗ Q) |
|---|---|---|
| 0 | Y, side | L0[t_Y] = B ⊗ ⟨t_Y⟩ |
| 1, 4 | Y, centre | L1 = B ⊗ D_j |
| 2 | X, side | L2[t_X] = (B ⊗ D_j) ⊥ (P ⊗ ⟨t_X⟩) |
| 3, 6 | X, centre | L3 = E ⊗ D_j |
| 5 | Y, side | L5[t_Y] = (B ⊗ D_j) ⊥ (P ⊗ t_Y^⊥) |
| 7 | X, side | L3 |

**Terminal labels.**

| Wire | Source label | Sink label |
|---|---|---|
| X_d | U_d = ⟨u_d⟩, u_d = t_{d₁} ⊗ t_{d₂} ⊗ t_{d₃} | A (full) |
| Y_d | 0 | U_d^⊥ |
| Auxiliary | 0 | A |

**Lemma 5.1 (cells) [proof].**
- Norms multiply under ⊗, so P and Q are lines of norm 1, hence nondegenerate. So E = B ⊥ P and Fu = Q ⊥ Q′, with B and Q′
  nondegenerate.
- In D_j we have D_j = ⟨t⟩ ⊥ t^⊥. For a neighbour pair (t_X·t_Y = 0, both norm 1), D_j = ⟨t_X⟩ ⊥ ⟨t_Y⟩ ⊥ N with
  N = ⟨t_X, t_Y⟩^⊥ of dimension h_j − 2, because the Gram matrix of (t_X, t_Y) is I₂.
- The *cells* are the products X ⊗ Y ⊗ Z of these atoms, with X ∈ {B, P}, Y an atom of D_j and Z ∈ {Q, Q′}.
  - A tensor product of nondegenerate spaces is nondegenerate (the Gram matrix is a Kronecker product).
  - Distinct cells are orthogonal, because (x⊗y⊗z)·(x′⊗y′⊗z′) = (x·x′)(y·y′)(z·z′).
  - So **A = ⊥ of all cells**.
- Every label in the tables is an orthogonal sum of cells, using t_Y^⊥ = ⟨t_X⟩ ⊥ N for side wires. Hence:
  - every label is nondegenerate;
  - inclusion of labels is inclusion of cell sets;
  - the residual of a nested pair is the orthogonal sum of the cells in the difference;
  - its dimension is the sum of the cell dimensions dim X·dim Y·dim Z, with dim B = e − 1, dim P = dim Q = 1 and
    dim Q′ = q − 1.

**Lemma 2.3′ (label sequences) [proof by Lemma 5.1].** In this table, ⊆ marks an increasing edge and ⊇ a decreasing one.

| Wire (stage j) | Label sequence | Residuals and their dimensions |
|---|---|---|
| X entry (rows 2, 3, 6, 7) | E⊗⟨t⟩ ⊆ L2[t] ⊆ L3 = L3 = L3 | B⊗t^⊥: (e−1)(h_j−1); then P⊗t^⊥: h_j − 1 |
| Y entry (rows 0, 1, 4, 5) | B⊗⟨t⟩ = L0[t] ⊆ L1 = L1 ⊆ L5[t] | B⊗t^⊥: (e−1)(h_j−1); then P⊗t^⊥: h_j − 1 |
| Side A_{ST} | 0 ⊆ L0[t_Y] ⊆ L2[t_X] ⊆ L5[t_Y] ⊆ L3 ⊆ A | B⊗⟨t_Y⟩: e−1; (B⊗t_Y^⊥) ⊥ (P⊗⟨t_X⟩): (e−1)(h_j−1)+1; P⊗N: h_j−2; P⊗⟨t_Y⟩: 1; (E⊗D_j)⊗Q′: m − e·h_j. **Total m.** |
| Centre | 0 ⊆ L1 ⊆ L3 ⊇ L1 ⊆ L3 ⊆ A | B⊗D_j: (e−1)h_j; P⊗D_j: h_j three times; then m − e·h_j. **Total m + 2h_j.** |

- The side edge L2[t_X] ⊆ L5[t_Y] is where the neighbour condition is used: it needs ⟨t_X⟩ ⊆ t_Y^⊥.
- The only decreasing edge is the centre's L3 → L1, of dimension h_j.

**Stage boundaries [proof].**
- The outgoing labels of stage j are E⊗D_j⊗Q on X and (P⊗⟨t⟩)^⊥_{E⊗D_j}⊗Q = L5[t] on Y. The latter equality holds because the
  complement of the cell P⊗⟨t⟩ in E⊗D_j is (B⊗D_j) ⊥ (P⊗t^⊥).
- With E⁺ = E⊗D_j and P⁺ = P⊗⟨t_{d_j}⟩, these are exactly the incoming labels E⁺⊗⟨t⁺⟩⊗Q⁺ and B⁺⊗⟨t⁺⟩⊗Q⁺ of stage j+1.
- At stage 1, B = 0 and E = P = F₃, so the incoming labels are U_d on X and 0 on Y. These are the source labels.
- At stage 3, Q = F₃ and Q′ = 0, so the outgoing labels are A and U_d^⊥. These are the sink labels.
- The X boundary edge (outgoing label of stage j → first touch L2 of stage j+1) has residual B⁺⊗t⁺^⊥. The Y boundary edge has
  residual 0.

**The count [proof].** Sum the residual dimensions wire by wire. The signed change along a wire is (sink dim − source dim),
and absolute values add twice the decreases:
- each bank X_d goes from 1 to m;
- each Y_d goes from 0 to m − 1, and then pays one correction kernel (Prop 2.4′, Theorem 1) or none (the pre-pass of
  Lemma 6.1, Theorems 1′ and 2);
- each side wire costs m;
- each centre wire costs m + 2h_j.

Write μ = 1 with the correction kernel and μ = 2 with the pre-pass. Then

  **s′_μ = Wm − 2N₀ + (2 − μ)N₀ + 2Σ_j I_j c_j h_j = Wm − μN₀ + 2Σ_j I_j c_j h_j**,

and for an instance with h_j = h, v_j = v, c_j = c in every factor (I_j = v², I₀ = 3v²):

  **Δ_μ := Wm − s′_μ = μN₀ − 2I₀ch = v²(μv − 6ch).**

- μ = 1 (Theorem 1): **Δ′ = v²(v − 6ch)**.
- μ = 2 (Theorems 1′ and 2): **Δ = 2v²(v − 3ch)**.

Δ_μ does not depend on the number of side wires: each side wire adds m to both Wm and s′. Side wires enter only through
W, in ε = Δ/(W*m). That is why E1's smaller side-wire set (§10) helps.

Checks:
- **Every edge by brute-force F₃ linear algebra in F₃^{h³}**, through nondegeneracy, nesting, the explicit residual, its
  dimension, an orthogonal basis, and the phase Σ n_j(z_j·y)² compared with Q(P_V y) − Q(P_U y) computed independently:
  - full network at h = 6 (`m5_xref_e2e.c`, reproduced: 22 336 425 steps);
  - one representative invocation per stage plus the d* bank path at h = 6, 7, 8, 9, 10 (`x1_e2e_rep.c`). Orbit-weighted
    totals equal the closed form exactly, and at h = 6 they equal the full brute force.
- The cell bookkeeping reproduces the brute-force per-stage numbers at h = 6, 7, 8 (`x1_exponent_count.py`).

**Remark 5.2 (isometry orbits; why one representative invocation suffices) [proof].** Each σ = (σ₁, σ₂, σ₃) ∈ Sym(h)³ acts on
A = (F₃^h)^{⊗3} by permuting coordinates within each factor. This is an isometry, and it maps t_T to t_{σT}. Every label is
built functorially from the t's: E, D and Fu are invariant, and P^⊥ maps to (σP)^⊥. So σ maps the label sequences of the
invocation indexed by (T_l)_{l≠j} to those of (σ_l T_l)_{l≠j}, and the bank path of d to that of σd.
- Nesting, nondegeneracy, residual dimension and the existence of an orthogonal basis are isometry invariants.
- Sym(h) is transitive on 4-subsets.
- Hence the v² invocations of a stage are images of one, and the N₀ bank paths are images of the d* path.

---

## 6. Prop 2.4′ (finite interface)

**Lemma 6.1 (orthogonal address change; the two-sided pre-pass) [proof].** Let u ∈ A = F₃^m with u·u = 1, U = ⟨u⟩, and
let e₁ be the first basis vector.
- (a) There is an isometry A of A (Ax·Ay = x·y) with Au = e₁, a product of at most two reflections
  σ_a(x) = x − 2(x·a)(a·a)⁻¹a (a·a ≠ 0).
- (b) Put (P_A g)(x) = g(A⁻¹x), an address permutation (free in circuits). Then P_A F = F P_A, and
  **P_A Φ_W P_A⁻¹ = Φ_{AW}** for every nondegenerate W.
- (c) **R_u := Φ_{U^⊥}Φ_U⁻¹ = M₁·C′^{⊗m}·M₂**, with M₁ = P_A⁻¹(D P₂₃ ⊗ I) and M₂ = (D ⊗ I)P_A. Here D = diag(1, ω², ω²)
  and P₂₃ act on the e₁ coordinate, and I is the identity on the other m − 1. M₁ and M₂ are monomial.
- (d) With f columns the same holds for R_u^{⊗f} = Φ_{U^⊥}^{⊗f}(Φ_U^{⊗f})⁻¹, with A, D and P₂₃ applied in every column.

**Proof.**
- (a) If u = e₁, take A = I. Otherwise put a = u − e₁ and b = u + e₁. Then a·a + b·b = 2(u·u + e₁·e₁) = 4 = 1, so they are
  not both 0.
  - If a·a ≠ 0, then a·a = 2(1 − u·e₁) and u·a = 1 − u·e₁, so 2(u·a)(a·a)⁻¹ = 1 and σ_a(u) = u − a = e₁.
  - Otherwise b·b ≠ 0, and in the same way σ_b(u) = u − b = −e₁. Then σ_{e₁}σ_b maps u to e₁.
  - Reflections preserve the dot product, since σ_a(x)·σ_a(y) = x·y − 4(x·a)(y·a)(a·a)⁻¹ + 4(x·a)(y·a)(a·a)⁻¹.
- (b) (F P_A g)(x) = Σ_y ω^{x·y} g(A⁻¹y) = Σ_y ω^{x·Ay} g(y) = Σ_y ω^{A⁻¹x·y} g(y) = (Fg)(A⁻¹x), using Ax·Ay = x·y. Also
  P_A D_φ P_A⁻¹ = D_{φ∘A⁻¹}. The isometry A⁻¹ maps AW onto W and (AW)^⊥ onto W^⊥, so P_W A⁻¹ = A⁻¹ P_{AW}, and
  Q(P_W A⁻¹y) = Q(P_{AW} y). Hence P_A Φ_W P_A⁻¹ = F D_{ω^{Q(P_{AW}y)}} F⁻¹ = Φ_{AW}.
- (c) By (b), P_A R_u P_A⁻¹ = Φ_{e₁^⊥}Φ_{⟨e₁⟩}⁻¹. Its phase is Q(P_{e₁^⊥}y) − Q(P_{⟨e₁⟩}y) = Σ_{i≥2} y_i² + 2y₁². Coordinate by
  coordinate (Lemma 3.3, and Lemma 3.4 for the phase 2s²), this is Frob(C′) ⊗ C′^{⊗(m−1)}. By Lemma 3.4,
  Frob(C′) = D P₂₃ C′ D, so P_A R_u P_A⁻¹ = (D P₂₃ ⊗ I)·C′^{⊗m}·(D ⊗ I). Conjugate back by P_A.
- (d) Every factor is a tensor power over the columns. ∎

Checked:
- `x1_prepass_check.py`: frames built on the Fourier side from their definition, for every norm-1 u at
  (m, f) = (1,1), (2,1), (3,1), (4,1), (1,2), (2,2). That is 42 lines, including non-coordinate ones such as (1,1,1,1).
  (c) holds 42/42 with the A of (a). Refuted control: a one-sided adapter (R_u·C′^{−⊗m} monomial) holds 0/42.
- `x1_real_arrays.py` mode 4: the pre-pass in a real network, described under Prop 2.4′ below.

> **Gotcha (the breaking site).** An *output-side* monomial alone can never remove the correction kernel: R_u·C′^{−⊗m} is
> not monomial for any u (0/42 above, and mode 5 of `x1_real_arrays.py` fails 18/18). The pre-pass works only because it
> has a monomial on **both** sides, M₂⁻¹ before the network on X_d and M₁⁻¹ after it on Y_d. An earlier draft of this repository
> concluded from the one-sided case that μ = 1 is forced for odd label primes. That conclusion was wrong.

**Proposition 2.4′.** For every f ≥ 1 and any number of spectator trits, the network applies C'^{⊗mf} to each of W arbitrary
arrays on (F₃^m)^f, after the bank exchange is undone by relabeling. It uses exactly s′_μ directional steps (§5): μ = 1
with the correction kernel and μ = 2 with the pre-pass. Each step is, after
an address permutation, 3^{(#other trits)} copies of C'^{⊗f} or Frob(C')^{⊗f} on fibres, and Frob(C')^{⊗f} =
D^{⊗f}P₂₃^{⊗f}C'^{⊗f}D^{⊗f}. All other work is a fixed number (independent of f) of pointwise F₂-linear gates and monomial
maps per address.

**Proof [proof].**
- By Lemma 4.1 the executed map is diag(Φ_sink^{⊗f})·𝒮·diag(Φ_source^{⊗f})⁻¹. By Lemma 2.1′, 𝒮 routes X_d → Y_d, Y_d → X_d,
  and each auxiliary to itself.
- **Ordinary routes.** For the routes Y_d → X_d and auxiliary → auxiliary, the source label is 0 and the sink label is A. The
  ratio is Φ_A = C'^{⊗m} per column (Lemma 3.3).
- **Exceptional route X_d → Y_d.** The ratio is Φ_{U^⊥}Φ_U⁻¹ with U = ⟨u⟩ and u·u = 1. Here Q(P_{U^⊥}y) = Q(y) − Q(P_U y) and
  Q(P_U y) = (u·y)², so the exponent is Q(y) − 2(u·y)² = Q(y) + (u·y)². The ratio is therefore Φ_A·K_{u,1}.
- **Correction (μ = 1, Theorem 1).** One directional step K_{u,2}^{⊗f}, applied to the Y_d array after its last edge,
  leaves C'^{⊗m} per column (Lemma 3.2).
- **Pre-pass (μ = 2, Theorems 1′ and 2).** Instead, load M₂⁻¹x into X_d, where x is the array meant for that role, and read
  M₁⁻¹ of the Y_d array at the end (Lemma 6.1, per column). By Lemma 4.1 the executed map is linear, and by Lemma 2.1′ it
  routes X_d to Y_d for arbitrary contents, so this role now computes M₁⁻¹·R_u^{⊗f}·M₂⁻¹·x = C'^{⊗mf}x. Every other
  role, auxiliaries included, is untouched: only the contents of X_d changed, and the network is correct for any contents.
  The frames, the Lucas centre and the side-wire nesting are unchanged. The correction kernel is dropped, so the count
  falls by exactly N₀, from s′₁ to s′₂.
- **Steps.** By Lemma 2.2′, an edge with residual ρ is ρ kernels K_{z,±n}^{⊗f}. By Lemma 3.4, each kernel is one C'^{⊗f} call
  per fibre, with monomials when the sign is negative. Summing gives s′_μ (§5).
- **Fixed work.** The labels, the bases and the address maps depend only on the fixed data, not on f. Spectator trits only
  index extra copies. The pre-pass costs one F₄ scalar per entry on the N₀ bank inputs and on the N₀ bank outputs, plus
  free relabelings; M₁ and M₂ depend only on u_d. ∎

Checked:
- **On real arrays, one recursion level with f ≥ 2** (`x1_real_arrays.py`). Every role, auxiliaries included, is compared with
  C'^{⊗mf} computed independently by Yates.
- **Config A:** factor 1 is the genuine 4-subset family of [6] with the genuine Lucas centre; m = 6, f = 2, arrays of 3¹² entries,
  W = 808, 6 084 steps = s′.
- **Config B:** B ≠ 0 with side wires in factor 2; m = 4, f = 2 and f = 3.
- Negative controls fail as expected. Without the correction kernel, 18/18 Y_d fail. With a wrong row-5 label there are
  60 nesting failures. With a Lucas centre of size ≤ 1, 60/60 X_d fail.
- **The pre-pass on real arrays** (`x1_real_arrays.py` mode 4: no correction kernel; M₂⁻¹ on every X_d input and M₁⁻¹ on
  every Y_d output). The bank vectors u_d here are Kronecker products of the family vectors, so most are not coordinate
  vectors.
  - Config A, f = 2: 0/688 auxiliary, 0/60 X_d and 0/60 Y_d failures, with steps = s′₁ − N₀ (`run_real_A_f2_pre.txt`).
  - Config B, f = 2 and f = 3: 0/102, 0/18 and 0/18 failures, with steps = s′₁ − N₀ (`run_real_B_pre.txt`).
  - Refuted control, mode 5 (the output monomial M₁⁻¹ alone): 18/18 Y_d fail (`run_real_B_pre_bad5.txt`).

**Why the genuine instance cannot be run on real arrays.** The smallest genuine instance with more than one bank entry is
h = 5 (v = 5), so m = 125 and a single column already has 3¹²⁵ ≈ 10⁵⁹·⁶ entries. The case h = 4 has v = 1 and no side wires,
and still m = 64. Definition 1.1 and every lemma above are stated for admissible data in general, so the toy configurations
test the same proposition with smaller factor spaces.

---

## 7. Thm 2.6′ (recursion): L_{F₄}(C'^{⊗k}) = O(3^k (k+1)^{θ′})

**Setup.**
- Fix admissible data with a saving Δ = Wm − s′_μ > 0 (§5): a label family, a centre, a side-wire set, h, and μ ∈ {1, 2}.
- Let W* = 3^w be the least power of 3 that is ≥ W.
- Put S′ = s′_μ + (W* − W)m = W*m − Δ, λ′ = S′/W* = m − Δ/W* and θ′ = log_m λ′.
- Each of the W* − W padding arrays uses m plain directional steps: C'^{⊗mf} is the product over i ∈ [m] of C'^{⊗f} on the i-th
  trit of every column.

**Theorem 2.6′.** L_{F₄}(C'^{⊗k}) = O(3^k (k+1)^{θ′}). In particular θ′ < 1. The three instances:

| Instance | h | v | c | d (side wires per entry) | m | W* | Δ | ε = Δ/(W*m) | 1 − θ′ |
|---|---|---|---|---|---|---|---|---|---|
| Theorem 1: 4-subsets, μ = 1 | 92 | 2 794 155 | 4 279 | 2 332 242 | 778 688 | 3⁵⁵ | 3 373 902 208 276 911 675 | 2.4837·10⁻¹⁴ | **1.8309·10⁻¹⁵** |
| Theorem 1′: 4-subsets, μ = 2 | 51 | 249 900 | 1 327 | 178 553 | 132 651 | 3⁴⁶ | 5 853 939 037 380 000 | 4.9792·10⁻¹² | **4.2213·10⁻¹³** |
| Theorem 2: E1, μ = 2 (§10) | 23 | 245 157 | 1 771 | 63 700 | 12 167 | 3⁴⁵ | 14 780 032 279 463 484 | 4.1118·10⁻¹⁰ | **4.3713·10⁻¹¹** |

Each h is the best one for its row (`x1_theorems.py` scans 60 ≤ h ≤ 200, 30 ≤ h ≤ 200 and 14 ≤ h ≤ 120). Δ > 0 holds exactly
for h ≥ 79, h ≥ 43 and h ≥ 20 respectively, across those ranges.

**Proof [proof, circuit model].**
- **The quantity.** Let T(k) be the gate count for applying C'^{⊗k} to W* arrays of length 3^k, and t(k) = T(k)/(W*3^k).
- **Base case.** Put K = m(w+1). For k < K, apply the k factors directly, at c_{C'}·3^{k−1} gates each, so t(k) ≤ B := K·c_{C'}.
- **Recursive step.** For k ≥ K, write k = mf + r with 0 ≤ r < m. Then f ≥ w + 1.
  - Apply the r leftover trits directly.
  - On W of the arrays, run Prop 2.4′ with f columns and r spectators. On the rest, use the plain steps. With μ = 2, every
    call re-applies M₂⁻¹ to its N₀ bank inputs and M₁⁻¹ to their outputs (Lemma 6.1). This is monomial work inside A below.
  - There are S′ directional steps. Each consists of 3^{k−f} fibre transforms C'^{⊗f} (or Frob(C')^{⊗f} = monomial·C'^{⊗f}·monomial).
  - Since k − f ≥ (m−1)(w+1) ≥ w, the number 3^{k−f} is divisible by W*. Partition the fibres of each step into 3^{k−f}/W*
    batches of W*, and apply the W*-array algorithm recursively to each batch.
  - All fibres in a batch come from one step, so they share the transform. The algorithm is valid on arbitrary values in all
    W* roles (Prop 2.4′, auxiliaries included), so the induction on k is sound.
- **The recurrence.** The fixed gates, monomials, corrections and leftover trits cost at most A·W*·3^k for a constant A that
  depends on h but not on k. So
  T(k) ≤ A·W*3^k + S′·(3^{k−f}/W*)·T(f), i.e. **t(k) ≤ A + λ′·t(⌊k/m⌋)**.
- **Unrolling.** Over d ≤ ⌈log_m(k+1)⌉ levels, t(k) ≤ A·Σ_{i<d}λ′^i + Bλ′^d ≤ (A/(λ′−1) + B)·λ′^d ≤ (A/(λ′−1) + B)·λ′·(k+1)^{θ′}.
- **One array.** Split off w axes: C'^{⊗k} = C'^{⊗w} ⊗ C'^{⊗(k−w)}. Run C'^{⊗(k−w)} on the 3^w = W* fibres as one batch, then
  apply C'^{⊗w} directly. This gives L(C'^{⊗k}) ≤ 3^k(t(k−w) + w·c_{C'}) = O(3^k(k+1)^{θ′}), with no factor W*.
- **The numbers.** They come from exact integer arithmetic and 60-digit Decimal (`x1_exponent_count.py` for Theorem 1,
  `x1_theorems.py` for all three rows). λ′/m = 1 − ε with ε = Δ/(W*m), and 1 − θ′ = −ln(1 − ε)/ln m. Lean encloses each
  value (README). ∎

**Count at h = 79, …, 92: a re-derivation from Lemma 5.1 [computation].** `x1_exponent_count.py` computes the count edge by edge, but its label sequences are transcribed from the cell tables of Lemma 5.1, so it is a re-derivation of the closed form from that lemma, not independent evidence for it at large h. Its independent parts are the enumeration of v, d_nbr and c, the nesting checks of the walk, and the agreement with brute-force F₃ linear algebra at h = 6, 7, 8, 9, 10 (parsed from the `run_rep_h*_bad0.txt` logs). It computes:
- v, the neighbour count of a 4-subset, and c, by enumerating the actual subsets;
- the step count as an edge-by-edge, orbit-weighted sum of cell dimensions.

At every h from 79 to 92 the result equals Wm − N₀ + 2I₀ch exactly. Δ′ is positive for 79 ≤ h ≤ 92 and negative at h = 78. The
best h is 92, where 1 − θ′ = 1.8309·10⁻¹⁵. For h from 93 to 120 this was checked with the closed form only; none of those
values does better. Brute-force linear algebra at h ≥ 79 is impossible, since m ≥ 493 039 and
one label basis is about m²/4 trits. The cell bookkeeping is the proved Lemma 5.1; the script checks that it agrees with brute force at
h = 6, 7, 8, 9, 10 (per stage, the d* path and the total).

**RAM model.** The preprint's Lemma 2.5 (address permutations in O(2^k) time) would transfer with radix-3^m digits, but this is
**[cite]/[arg]** and **not used**: in circuits, permutations are free.

---

## 8. Transfer to M_k = S^{⊗k} over F₂, with S = [[1,0],[1,1]]

**Step T1: explicit word [proof by exact computation].** Over F₁₆ = F₂[x]/(x⁴+x+1) we have ω = x⁵, and

  **S⊗S = M₀·Π₁(C'⊕1)Π₁⁻¹·M₁ ⋯ Π₁₂(C'⊕1)Π₁₂⁻¹·M₁₂**,

with 12 slots. Each Π_i is a permutation of the four coordinates and each M_i is a monomial matrix over F₁₆.
- The word was found by our own search (`proofs/WORD.md`, and `m6_word_*` in `certificates/`).
- It was **re-verified with independent code** in `x1_word_check.py`. The three 4-slot transvection words evaluate as stated,
  their embedded product is exactly S⊗S, every slot is monomial or a permutation conjugate of C'⊕1, and the mixed product at
  t = 2 gives S^{⊗4}.
- Only the forward C' appears. **This removes Ostrom–Wagner and the 2-transitivity computation from the proof.**

**Step T2: mixed product [proof].** Let k = 2t and N = 4^t. Because (AB)^{⊗t} = A^{⊗t}B^{⊗t}, M_k = (S⊗S)^{⊗t} is the
product of the 13 monomial factors M_i^{⊗t}, interleaved with the 12 factors (Π_i^{⊗t})(C'⊕1)^{⊗t}(Π_i^{⊗t})⁻¹.
- Π_i^{⊗t} is a permutation, which is free.
- M_i^{⊗t} is monomial: one fixed F₁₆ scalar per entry, so N multiplications.

**Step T3: sectors [proof].** For R ⊆ [t], let V_R be the span of the basis vectors e_{i₁…i_t} with i_j ∈ {0,1,2} exactly for
j ∈ R.
- The V_R are coordinate subspaces with disjoint supports covering all 4^t coordinates.
- (C'⊕1)^{⊗t} preserves each V_R and acts on it as C'^{⊗|R|}.
- So L((C'⊕1)^{⊗t}) ≤ Σ_r C(t,r)·L(C'^{⊗r}).
- **F₁₆ data.** The F₄-circuit of Thm 2.6′ is linear with coefficients in F₄ ⊆ F₁₆, so it computes the same map on F₁₆-valued
  arrays. Alternatively, F₁₆ = F₄ ⊕ F₄β, and the circuit runs once per component.

**Step T4: Jensen [proof].** Write L(C'^{⊗r}) ≤ A′3^r(r+1)^{θ′} for all r ≥ 0. Then
Σ_r C(t,r)A′3^r(r+1)^{θ′} = A′4^t·E[(R+1)^{θ′}] with R ~ Bin(t, 3/4). Since x ↦ (x+1)^{θ′} is concave, this is
≤ A′4^t(3t/4 + 1)^{θ′}.

**Step T5: descent to F₂ [proof].**
- Write each F₁₆ wire as 4 F₂ wires.
- Multiplication by a fixed α is a 4×4 F₂ matrix, costing ≤ 12 XORs. So a gate αu + βv costs ≤ 28 XORs.
- *Note (loose constant).* The theorem below charges every F₁₆ operation 28 XORs, including the 13N monomial scalings, which are
  single multiplications and need only ≤ 12. The bound is therefore loose but correct; only the constant changes, not θ′.
- M_k has 0/1 entries, so on F₂ inputs (embedded as (x,0,0,0)) the outputs lie in F₂. Read off component 0.

**Step T6: odd k [proof].** M_{k+1} = [[M_k, 0], [M_k, M_k]]. Feed (x, 0) and read the first half.

**Theorem X1 [proof, given §§1–7].**

  **L_{F₂}(M_k) ≤ 28·(12·A′·N·(3t/4 + 1)^{θ′} + 13N) = O(N (log N)^{θ′}),**

with θ′ the exponent of any row of Thm 2.6′: 1 − θ′ = 1.83·10⁻¹⁵ (Theorem 1), 4.22·10⁻¹³ (Theorem 1′) or 4.37·10⁻¹¹
(Theorem 2). In particular L_{F₂}(M_k) = o(N log N). Steps T1–T6 use only the F₄ bound, so they apply to every row
unchanged.

**Crossover [arg].** The pipeline beats Yates (kN/2 XORs) once (1 − ε)^d < 1/c₀, where:
- d ≈ log_m k is the number of recursion levels;
- c₀ is the ratio of constant factors (word slots × XORs per C' × 1/(3/4), against Yates).

So log₁₀ k ≈ log₁₀ m · ln c₀/ε, with each row's own m and ε (`x1_theorems.py`):

| c₀ | Theorem 1 (m = 778 688) | Theorem 1′ (m = 132 651) | Theorem 2 (m = 12 167) |
|---|---|---|---|
| 2 | 1.6·10¹⁴ | 7.1·10¹¹ | 6.9·10⁹ |
| 84 (WORD's explicit constant) | 1.05·10¹⁵ | 4.6·10¹² | 4.4·10¹⁰ |
| 10⁶ | 3.3·10¹⁵ | 1.4·10¹³ | 1.4·10¹¹ |

**The crossover is at log₁₀ k ~ 10¹⁵, 10¹² and 10¹⁰–10¹¹ for the three rows.** Nothing is witnessed at any feasible size.

---

## 9. What is re-proved and what is cited

| Preprint step | Flipped statement here | Status |
|---|---|---|
| Lemma 2.1 (scalar network, RG + JV = I, three stages, arbitrary auxiliaries) | Lemma 1.2 + Lemma 2.1′ | **re-proved** [proof]; executed over all invocations, h ≤ 10 |
| Frame definition, Φ_D = C^{⊗m}, characters ↔ translations | §0, Lemmas 3.1–3.3 | **re-proved** [proof] |
| Lemma 2.2 (edges = ρ kernels, inverse = forward + translation) | Lemma 2.2′, Lemma 3.4 (inverse = forward + monomials) | **re-proved** [proof] |
| Telescoping (gates commute with frames) | Lemma 4.1 | **re-proved** [proof] |
| Lemma 2.3 (labels nested and nondegenerate, orthonormal bases, the count s, Δ) | Lemma 5.1, Lemma 2.3′, the count s′ and Δ′; no h ≥ 7 condition needed | **re-proved** [proof]; brute force h = 6..10 |
| Prop 2.4 (finite interface, exceptional route) | Prop 2.4′ (one correction kernel per bank entry) | **re-proved** [proof]; real arrays, f = 2, 3 |
| (not in the preprint, whose exceptional route is corrected at the sink only) a two-sided monomial pre-pass in place of the correction kernel | Lemma 6.1, Prop 2.4′ with μ = 2 | **new** [proof]; Fourier-side check on 42 lines; real arrays, f = 2, 3 |
| (not in the preprint) 7-subset labels with a 3-subset centre | §10, Theorem 2 | **new** [proof]; one invocation at h = 11, 12; no full network run |
| Lemma 2.5 (RAM address permutations in O(2^k)) | not needed (circuit model) | **still cited**, unused |
| Thm 2.6 (fibre batching, recurrence, exponent) | Thm 2.6′ in the circuit model, W* = 3⁵⁵ | **re-proved** [proof]; constants exact |
| (not in the preprint) generation of the transfer group | explicit 12-slot word (WORD.md), re-verified | [proof by computation]; Ostrom–Wagner **no longer cited** |
| (not in the preprint) transfer to M_k | §8 T2–T6 | [proof] |

**What remains outside this document:**
- A human referee of §§1–10.
- The RAM-model statement, which is not claimed.
- Any odd label prime other than p = 3. Lemma 6.1 is proved only for p = 3.

---

## 10. Theorem 2: the E1 gadget (7-subset labels, 3-subset centre)

*Status: written proof; refereed once by an AI agent, not by a human. No full 7-set network has been run. The largest
executed piece is one scalar invocation at h = 11 and 12.*

**The instance.**
- h_j = h for every j. 𝒯 is the set of indicators of the 7-subsets of [h], so v = C(h, 7). Their norm is 7 ≡ 1, and
  t_S·t_T = |S∩T| mod 3. So S, T are neighbours iff |S∩T| ∈ {0, 3, 6}.
- The centre has one wire c_P for each P ⊆ [h] with |P| = 3, so c = C(h, 3). As in §1, (Gx)_P = Σ_{T⊇P} x_T and
  (Rc)_S = Σ_{P⊆S} c_P, and J = RG on neighbour pairs.
- The side-wire set is the support of J: the ordered pairs with |S∩T| = 3 (Lemma 10.1). There are
  **d = C(7,3)·C(h−7, 4) = 35·C(h−7, 4)** of them per entry: choose the 3 shared points inside S and the 4 others outside.
  The neighbour pairs with |S∩T| ∈ {0, 6} carry no side wire.
- The exceptional route uses the pre-pass (μ = 2).

**Lemma 10.1 (the E1 centre) [proof].**
- (RG)_{ST} = #{P ⊆ S∩T : |P| = 3} = C(n, 3) with n = |S∩T|.
- By Lucas' theorem, or directly from C(n,3) = 0, 0, 0, 1, 4, 10, 20, 35 for n = 0, …, 7, this is odd exactly at n ∈ {3, 7}.
- So RG = 1 on the diagonal (n = 7), RG = 0 on non-neighbours (n ∈ {1, 2, 4, 5}), and RG = 0 on the neighbours with n ∈ {0, 6}.
  With J := RG on neighbours, RG + JV = I, and J is supported exactly on the pairs with n = 3.

Checked: Lean `MobiusLean.LucasE1` (for every finite type: the Finset count and the table). `x1_e1_check.py` runs one
forward invocation over F₄ with random values on every wire and side wires only on the n = 3 pairs, at h = 11
(v = 330) and h = 12 (v = 792). It gives 0 failures, restores every auxiliary, and its side-wire counts equal
35·C(h−7, 4). Refuted controls: a 2-subset centre at h = 12 gives 1 214 failures, and the 3-subset centre without J gives
468. (A 2-subset control at h = 11 would pass vacuously, because two 7-subsets of [11] meet in at least 3 points.)

**Cell structure [proof].** Lemma 5.1 used only three facts about the family: each t has norm 1; neighbours are
orthogonal; and for a pair (t_X, t_Y) on a side wire, the Gram matrix of (t_X, t_Y) is I₂. All three hold here, since
7 ≡ 1 and 3 ≡ 0 mod 3. So D_j = ⟨t_X⟩ ⊥ ⟨t_Y⟩ ⊥ N on every side wire, the cells and label tables of §5 apply verbatim, and
every label is nondegenerate and nested as before. Remark 5.2 carries over: Sym(h) is transitive on 7-subsets and on
ordered pairs with |S∩T| = 3, so one representative invocation and one bank path describe all of them. Lemma 2.1′
holds with the side-wire set 𝒩 = supp J (§1).

**The count [proof].** By §5, with μ = 2,

  **Δ = 2N₀ − 2I₀ch = 2v²(v − 3ch)**, with v = C(h,7), c = C(h,3), and
  W = 2v³ + 3v²(v·35·C(h−7,4) + C(h,3)).

- Δ > 0 exactly for h ≥ 20 (scanned to h = 120; Lean checks h ∈ [20, 60] positive and h ∈ [7, 19] negative). Without the
  pre-pass (μ = 1) the threshold is h ≥ 23.
- The best h under Thm 2.6′ is h = 23: W* = 3⁴⁵, ε = 4.1118·10⁻¹⁰, and **1 − θ′ = 4.3713·10⁻¹¹**.
- The cell walk of `x1_exponent_count.py`, with this family's v, c and d, equals the closed form at h = 11, 12, 20, 23
  (`x1_theorems.py`). This is a re-derivation from Lemma 5.1, as for Theorem 1.

**Theorem 2 [proof, given §§1–8 and Lemma 10.1].** L_{F₂}(M_k) = O(N (log N)^{θ′}) with 1 − θ′ = 4.37·10⁻¹¹.

---

## 11. Open: whole-residual batching (a conjecture, not a theorem)

Thm 2.6′ spends one directional step per kernel: an edge of residual dimension ρ costs ρ calls of C′^{⊗f}. A faster
recursion would spend one call of C′^{⊗ρf} per residual. θ would then solve Σ_e (ρ_e/m)^θ = W over the residual histogram
of one level.

**Conjecture.** That recurrence can be made rigorous for the flipped network, with its padding and partial batches. If
so, E1 with the pre-pass would give 1 − θ ≈ 3.98·10⁻⁹ (h = 21; `x1_theorems.py --conjecture`).

**What is missing.** The recurrence itself, with padding and partial batches, is not written or proved here. The value
3.98·10⁻⁹ is computed **without** padding. **No statement in this repository depends on this conjecture.**
