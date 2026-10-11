set_option autoImplicit false
/-!
# Parameters of the genuine instance (no Mathlib import, so small kernel checks stay light)

`v h = C(h,4)`, `c h = 1 + h + C(h,2)`, `d h = C(h-4,4) + 4(h-4)`, written as falling products (these are
`Nat.descFactorial` unfolded; `MobiusLean.Numeric` proves the equalities with `Nat.choose`).
-/

namespace Mob

def v (h : Nat) : Nat := (h - 3) * ((h - 2) * ((h - 1) * (h * 1))) / 24
def c (h : Nat) : Nat := 1 + h + (h - 1) * (h * 1) / 2
def d (h : Nat) : Nat := (h - 4 - 3) * ((h - 4 - 2) * ((h - 4 - 1) * ((h - 4) * 1))) / 24 + 4 * (h - 4)
def m (h : Nat) : Nat := h ^ 3
def N0 (h : Nat) : Nat := v h ^ 3
def I0 (h : Nat) : Nat := 3 * v h ^ 2
def W (h : Nat) : Nat := 2 * N0 h + 3 * v h ^ 2 * (v h * d h + c h)
/-- The step count `s' = W m - N₀ + 2 I₀ c h` of Lemma 2.3′. -/
def steps (h : Nat) : Int := (Int.ofNat (W h)) * (Int.ofNat (m h)) - (Int.ofNat (N0 h)) + 2 * (Int.ofNat (I0 h)) * (Int.ofNat (c h)) * (Int.ofNat (h))
/-- The saving per level, `Δ' = W m - s'`. -/
def Δ' (h : Nat) : Int := (Int.ofNat (W h)) * (Int.ofNat (m h)) - steps h


end Mob
