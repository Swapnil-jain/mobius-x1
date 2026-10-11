import MobiusLean.Defs
set_option autoImplicit false
/-!
# Parameters with the two-sided pre-pass (no Mathlib, so the kernel checks stay light)

With the pre-pass of PROOF.md Prop 2.4′ the exceptional route needs no correction kernel, so the step count loses
one step per bank entry: `s₂ = W m - 2 N₀ + 2 I₀ c h` and the saving is `Δ₂ = W m - s₂ = 2 N₀ - 2 I₀ c h`
(`μ = 2`). This file states it for the 4-subset family of `MobiusLean.Defs` (Theorem 1′) and for the E1 family
(Theorem 2): 7-subsets of `[h]` (`vE h = C(h,7)`), centre = all 3-subsets (`cE h = C(h,3)`), and side wires only on
the J-supported pairs `|S ∩ T| = 3` (`dE h = 35 C(h-7,4)` per entry). Binomials are falling products;
`MobiusLean.Prepass` ties them to `Nat.choose`.
-/

namespace Mob

/-- Step count of the 4-subset network with the pre-pass (no correction kernel). -/
def steps₂ (h : Nat) : Int :=
  (Int.ofNat (W h)) * (Int.ofNat (m h)) - 2 * (Int.ofNat (N0 h)) + 2 * (Int.ofNat (I0 h)) * (Int.ofNat (c h)) * (Int.ofNat h)
/-- Saving per level with the pre-pass, `Δ₂ = W m - s₂`. -/
def Δ₂ (h : Nat) : Int := (Int.ofNat (W h)) * (Int.ofNat (m h)) - steps₂ h

/-! ## The E1 family -/

def vE (h : Nat) : Nat := (h - 6) * ((h - 5) * ((h - 4) * ((h - 3) * ((h - 2) * ((h - 1) * (h * 1)))))) / 5040
def cE (h : Nat) : Nat := (h - 2) * ((h - 1) * (h * 1)) / 6
def dE (h : Nat) : Nat := 35 * ((h - 7 - 3) * ((h - 7 - 2) * ((h - 7 - 1) * ((h - 7) * 1))) / 24)
def N0E (h : Nat) : Nat := vE h ^ 3
def I0E (h : Nat) : Nat := 3 * vE h ^ 2
def WE (h : Nat) : Nat := 2 * N0E h + 3 * vE h ^ 2 * (vE h * dE h + cE h)
/-- E1 step count with the pre-pass. -/
def stepsE (h : Nat) : Int :=
  (Int.ofNat (WE h)) * (Int.ofNat (m h)) - 2 * (Int.ofNat (N0E h)) + 2 * (Int.ofNat (I0E h)) * (Int.ofNat (cE h)) * (Int.ofNat h)
def ΔE (h : Nat) : Int := (Int.ofNat (WE h)) * (Int.ofNat (m h)) - stepsE h
/-- E1 WITHOUT the pre-pass (one correction kernel per bank entry, `μ = 1`), used only as a refuted control. -/
def ΔE₁ (h : Nat) : Int := (Int.ofNat (N0E h)) - 2 * (Int.ofNat (I0E h)) * (Int.ofNat (cE h)) * (Int.ofNat h)

end Mob
