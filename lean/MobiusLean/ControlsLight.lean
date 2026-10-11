import MobiusLean.Brute
import MobiusLean.Word
set_option autoImplicit false

/-! # Refuted controls for the Lucas identity, the counts and the word (no Mathlib). -/

namespace Mob

/-- A centre of size `≤ 1` (no pairs) breaks `RG + JV = I`. -/
theorem ctl_centre_small : idOK 6 1 = false := by decide +kernel

/-- Without the neighbour correction `J`, `RG ≠ I` (neighbours with `|S ∩ T| = 0` or `3` have odd entries). -/
def idNoJ (h : Nat) : Bool :=
  (quads h).all fun S => (quads h).all fun T => rg h 2 S T == (if S == T then 1 else 0)
theorem ctl_no_J : idNoJ 6 = false := by decide +kernel

/-- Neighbours defined mod 2 instead of mod 3 (characteristic-2 labels) break the identity. -/
def idMod2 (h : Nat) : Bool :=
  (quads h).all fun S => (quads h).all fun T =>
    let n := pc h (S &&& T)
    let r := rg h 2 S T
    let j := if S != T && n % 2 == 0 then r else 0
    (r + j) % 2 == (if S == T then 1 else 0)
theorem ctl_mod2 : idMod2 6 = false := by decide +kernel

/-- A wrong neighbour count (`3 (h-4)` in place of `4 (h-4)`) fails the enumeration. -/
theorem ctl_d_formula :
    ((quads 9).filter fun T => T != 15 && pc 9 (T &&& 15) % 3 == 0).length ≠
      (9 - 4 - 3) * ((9 - 4 - 2) * ((9 - 4 - 1) * ((9 - 4) * 1))) / 24 + 3 * (9 - 4) := by decide +kernel

open W in
/-- Changing one diagonal entry of the type-A core breaks the word. -/
theorem ctl_word : prod ((([T1, T2a, ⟨T2b.M0, [[1, 2, 8], [1, 5, 6], [1, 5, 5]], T2b.M1, T2b.coords, T2b.val⟩] :
    List Factor).flatMap fun F => (slots3 F).map fun X => embed X F.coords)) 4 ≠ SS := by decide +kernel

open W in
/-- Changing `D₄` breaks the `S ⊕ 1` word. -/
theorem ctl_s1 : prod ([s1M0] ++ word [[1, 1, 2], [1, 1, 14], [1, 4, 11], [1, 14, 4]] ++ [s1M1]) 3 ≠ S1 := by
  decide +kernel

open W in
/-- `C′` is not its own Frobenius image and has order 3, not 2. -/
theorem ctl_kernel : Cp ≠ frob Cp ∧ mmul Cp Cp ≠ eye 3 := by decide +kernel

end Mob
