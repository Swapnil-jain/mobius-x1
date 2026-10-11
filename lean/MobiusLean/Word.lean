set_option autoImplicit false

/-!
# The transfer word over F₁₆ (PROOF.md §8 Step T1, `x1/WORD.md`) and the 3 × 3 kernel identities

F₁₆ = F₂[x]/(x⁴ + x + 1), elements as `Nat` in `[0, 16)` with bit `i` the coefficient of `xⁱ`; addition is `^^^`,
multiplication is carry-less with reduction (`gmul`). `field_ok` checks by exhaustion that this is a commutative
ring with 16 elements in which every nonzero element is invertible, i.e. the field F₁₆. ω = x⁵ = 6, ω² = 7.

Checked (`decide +kernel`, no Mathlib):
* `omega_ok`: ω² = 7, ω³ = 1, 1 + ω + ω² = 0 (so ω generates F₄ ⊆ F₁₆);
* `kernel_ok`: C′ = ωI + ω²J₃, C′³ = I, C′² = Frob(C′), and Frob(C′) = D·P₂₃·C′·D with D = diag(1, ω², ω²) (Lemma 3.4);
* `s1_ok`: the width-3 word M₀·C′D₁C′D₂C′D₃C′D₄C′·M₁ = S ⊕ 1 (5 C′-slots);
* `factors_ok`: the three 4-slot transvection words T₁, T₂ₐ, T₂ᵦ evaluate to the stated 3 × 3 matrices;
* `word_ok`: the 27 embedded 4 × 4 slots (12 copies of C′ on 3 coordinates, 15 monomials) multiply to exactly S ⊗ S,
  every non-C′ slot is monomial, and a C′ slot on coordinates {0,2,3} or {1,2,3} is a permutation conjugate of C′ ⊕ 1.
-/

namespace Mob.W

/-- Multiplication by `x` in F₁₆. -/
def xt (a : Nat) : Nat := if (a <<< 1) &&& 16 != 0 then (a <<< 1) ^^^ 19 else a <<< 1

/-- Carry-less product reduced mod `x⁴ + x + 1`, by four shift-and-add rounds. -/
def gmul (a b : Nat) : Nat :=
  let r0 := if b &&& 1 != 0 then a else 0
  let a1 := xt a
  let r1 := if b &&& 2 != 0 then r0 ^^^ a1 else r0
  let a2 := xt a1
  let r2 := if b &&& 4 != 0 then r1 ^^^ a2 else r1
  let a3 := xt a2
  if b &&& 8 != 0 then r2 ^^^ a3 else r2

def F16 : List Nat := List.range 16

def field_ok : Bool :=
  F16.all fun a => F16.all fun b =>
    gmul a b < 16 && gmul a b == gmul b a && gmul a 1 == a &&
    F16.all fun c => gmul (gmul a b) c == gmul a (gmul b c) &&
      gmul a (b ^^^ c) == (gmul a b ^^^ gmul a c)
def inv_ok : Bool := (List.range 15).all fun i => F16.any fun b => gmul (i + 1) b == 1

theorem field_ok_true : field_ok = true := by decide +kernel
theorem inv_ok_true : inv_ok = true := by decide +kernel

def ω : Nat := 6
theorem omega_ok : gmul ω ω = 7 ∧ gmul ω (gmul ω ω) = 1 ∧ (1 ^^^ ω ^^^ gmul ω ω) = 0 ∧
    ω = xt (xt (xt (xt (xt 1)))) := by decide +kernel

/-! ## Matrices over F₁₆ as lists of rows -/

abbrev Mat := List (List Nat)

def ent (A : Mat) (i j : Nat) : Nat := (A.getD i []).getD j 0
def xsum (l : List Nat) : Nat := l.foldl (· ^^^ ·) 0
def mmul (A B : Mat) : Mat :=
  (List.range A.length).map fun i => (List.range (B.headD []).length).map fun j =>
    xsum ((List.range B.length).map fun l => gmul (ent A i l) (ent B l j))
def eye (n : Nat) : Mat := (List.range n).map fun i => (List.range n).map fun j => if i == j then 1 else 0
def diag (d : List Nat) : Mat :=
  (List.range d.length).map fun i => (List.range d.length).map fun j => if i == j then d.getD i 0 else 0
def prod (l : List Mat) (n : Nat) : Mat := l.foldl mmul (eye n)

def Cp : Mat := [[1, 7, 7], [7, 1, 7], [7, 7, 1]]
def J3 : Mat := [[1, 1, 1], [1, 1, 1], [1, 1, 1]]
def madd (A B : Mat) : Mat := List.zipWith (List.zipWith (· ^^^ ·)) A B
def smul (a : Nat) (A : Mat) : Mat := A.map (·.map (gmul a))
def frob (A : Mat) : Mat := A.map (·.map fun x => gmul x x)
def P23 : Mat := [[1, 0, 0], [0, 0, 1], [0, 1, 0]]

theorem kernel_ok :
    Cp = madd (smul ω (eye 3)) (smul (gmul ω ω) J3) ∧ prod [Cp, Cp, Cp] 3 = eye 3 ∧
      mmul Cp Cp = frob Cp ∧ frob Cp = prod [diag [1, 7, 7], P23, Cp, diag [1, 7, 7]] 3 := by
  decide +kernel

/-- `C′ D₁ C′ D₂ ⋯ C′`. -/
def word (ds : List (List Nat)) : List Mat := Cp :: ds.flatMap fun d => [diag d, Cp]

def S1 : Mat := [[1, 0, 0], [1, 1, 0], [0, 0, 1]]
def s1M0 : Mat := [[0, 2, 0], [0, 0, 5], [4, 0, 0]]
def s1M1 : Mat := [[0, 0, 1], [1, 0, 0], [0, 5, 0]]
def s1D : List (List Nat) := [[1, 1, 2], [1, 1, 14], [1, 4, 11], [1, 14, 3]]

theorem s1_ok : prod ([s1M0] ++ word s1D ++ [s1M1]) 3 = S1 := by decide +kernel

/-! ## S ⊗ S at width 4 (coordinates 00, 01, 10, 11 → 0, 1, 2, 3) -/

def SS : Mat := (List.range 4).map fun i => (List.range 4).map fun j =>
  if j / 2 ≤ i / 2 && j % 2 ≤ i % 2 then 1 else 0

def dsA : List (List Nat) := [[1, 2, 7], [1, 5, 6], [1, 5, 5]]
def dsB : List (List Nat) := dsA.reverse

/-- One factor: `(M₀, D-list, M₁, coordinates, stated 3×3 value)`. -/
structure Factor where
  M0 : Mat
  ds : List (List Nat)
  M1 : Mat
  coords : List Nat
  val : Mat

def T1 : Factor := ⟨[[0, 0, 12], [0, 4, 0], [15, 0, 0]], dsB, [[0, 6, 0], [0, 0, 1], [1, 0, 0]], [0, 1, 2],
  [[1, 0, 0], [1, 1, 0], [1, 0, 1]]⟩
def T2a : Factor := ⟨[[0, 15, 0], [2, 0, 0], [0, 0, 15]], dsA, diag [1, 12, 10], [0, 2, 3],
  [[1, 0, 0], [0, 1, 0], [1, 2, 1]]⟩
def T2b : Factor := ⟨[[0, 15, 0], [13, 0, 0], [0, 0, 15]], dsA, diag [1, 10, 10], [1, 2, 3],
  [[1, 0, 0], [0, 1, 0], [1, 3, 1]]⟩

def slots3 (F : Factor) : List Mat := [F.M0] ++ word F.ds ++ [F.M1]

/-- Embed a 3×3 matrix on `coords` of F₁₆⁴, identity on the remaining coordinate. -/
def embed (A : Mat) (cs : List Nat) : Mat :=
  (List.range 4).map fun i => (List.range 4).map fun j =>
    match cs.idxOf? i, cs.idxOf? j with
    | some a, some b => ent A a b
    | _, _ => if i == j then 1 else 0

def isMono (A : Mat) : Bool :=
  A.all (fun r => (r.filter (· != 0)).length == 1) &&
    (List.range A.length).all fun j => ((A.map fun r => r.getD j 0).filter (· != 0)).length == 1

def factors : List Factor := [T1, T2a, T2b]
/-- The 27 width-4 slots, tagged `true` for a copy of C′. -/
def slots : List (Bool × Mat) :=
  factors.flatMap fun F => (slots3 F).map fun X => (X == Cp, embed X F.coords)

theorem factors_ok : factors.all (fun F => prod (slots3 F) 3 == F.val) = true := by decide +kernel

/-- Permutation matrix sending `e_j ↦ e_{p j}`. -/
def perm (p : List Nat) : Mat := (List.range 4).map fun i => (List.range 4).map fun j =>
  if p.getD j 0 == i then 1 else 0
def tr (A : Mat) : Mat := (List.range 4).map fun i => (List.range 4).map fun j => ent A j i

theorem word_ok :
    prod (slots.map Prod.snd) 4 = SS ∧ (slots.filter Prod.fst).length = 12 ∧ slots.length = 27 ∧
      (slots.all fun s => s.1 || isMono s.2) = true ∧
      mmul (mmul (perm [0, 2, 3, 1]) (embed Cp [0, 1, 2])) (tr (perm [0, 2, 3, 1])) = embed Cp [0, 2, 3] ∧
      mmul (mmul (perm [1, 2, 3, 0]) (embed Cp [0, 1, 2])) (tr (perm [1, 2, 3, 0])) = embed Cp [1, 2, 3] := by
  decide +kernel

end Mob.W
