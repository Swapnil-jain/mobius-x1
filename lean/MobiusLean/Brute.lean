import MobiusLean.Defs
set_option autoImplicit false

/-!
# Brute force on bitmasks (no Mathlib; independent of the Finset proof in `MobiusLean.Lucas`)

`idOK h 2` evaluates `RG + JV = I` over F₂ entry by entry, over all ordered pairs of 4-subsets of `[h]`, with
the centre = all subsets of size ≤ 2 and `J = RG` on neighbour pairs (`|S ∩ T| ≡ 0 mod 3`, `S ≠ T`). It holds at
`h = 6, 7`. `dOK h` checks `v h`, the neighbour count `d h` of `T₀ = {0,1,2,3}` and `c h` by enumeration.
-/

namespace Mob

/-! ## Brute force on bitmasks -/

/-- Population count of the low `k` bits. -/
def pc : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + pc k (n / 2)

def quads (h : Nat) : List Nat := (List.range (2 ^ h)).filter fun S => pc h S == 4
/-- The centre wires: all subsets of size `≤ s` (the genuine centre has `s = 2`). -/
def centre (h s : Nat) : List Nat := (List.range (2 ^ h)).filter fun P => pc h P ≤ s
/-- `(RG)_{ST} mod 2` with a centre of subsets of size `≤ s`. -/
def rg (h s S T : Nat) : Nat := ((centre h s).filter fun P => (P &&& (S &&& T)) == P).length % 2

/-- `RG + JV = I` over F₂, entry by entry, with `J = RG` on neighbour pairs. -/
def idOK (h s : Nat) : Bool :=
  (quads h).all fun S => (quads h).all fun T =>
    let n := pc h (S &&& T)
    let rgST := rg h s S T
    let jST := if S != T && n % 3 == 0 then rgST else 0
    (rgST + jST) % 2 == (if S == T then 1 else 0)

theorem lucas_identity_h6 : idOK 6 2 = true := by decide +kernel
theorem lucas_identity_h7 : idOK 7 2 = true := by decide +kernel

/-- `v` and the neighbour count `d` (of `T₀ = {0,1,2,3}`) by enumeration. -/
def dOK (h : Nat) : Bool :=
  (quads h).length == v h &&
    ((quads h).filter fun T => T != 15 && pc h (T &&& 15) % 3 == 0).length == d h &&
    (List.range (2 ^ h)).countP (fun P => pc h P ≤ 2) == c h

theorem counts_h8 : dOK 8 = true := by decide +kernel
theorem counts_h9 : dOK 9 = true := by decide +kernel
theorem counts_h10 : dOK 10 = true := by decide +kernel

end Mob
