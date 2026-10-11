import MobiusLean.Prepass
import MobiusLean.LucasE1

/-! # Refuted controls for Theorems 1′ and 2: each perturbed statement is proved false by the kernel. -/

namespace Mob

/-- The pre-pass saving is not positive at `h = 42` (4-subsets) or `h = 19` (E1): the thresholds are sharp. -/
theorem ctl_delta2_42 : ¬ (0 < Δ₂ 42) := by decide +kernel
theorem ctl_deltaE_19 : ¬ (0 < ΔE 19) := by decide +kernel

/-- Without the pre-pass (one correction kernel per bank entry, `μ = 1`), E1 has no saving at `h = 20`. -/
theorem ctl_deltaE1_20 : ¬ (0 < ΔE₁ 20) := by decide +kernel

/-- One power of 3 fewer roles is not enough: `W* = 3^46` and `3^45` are forced. -/
theorem ctl_Wstar_51 : ¬ (W 51 ≤ 3 ^ 45) := by decide +kernel
theorem ctl_WstarE_23 : ¬ (WE 23 ≤ 3 ^ 44) := by decide +kernel

/-- The `ε` bounds are tight in the last digit. -/
theorem ctl_eps51 : ¬ ((49792043456 / 10 ^ 22 : ℚ) < ε51) := by decide +kernel
theorem ctl_epsE23 : ¬ (εE23 < 41118324737 / 10 ^ 20) := by decide +kernel

/-- Raising the lower end of either `1 - θ′` enclosure by one unit in the last digit breaks its rational check. -/
theorem ctl_theta1p_lo :
    ¬ ((422128278 / 10 ^ 21 : ℚ) * (1179547689818 / 10 ^ 11) ≤ lsum ε51 3 - lrem ε51 3) := by decide +kernel
theorem ctl_theta2_lo :
    ¬ ((437127525 / 10 ^ 19 : ℚ) * (940648264779 / 10 ^ 11) ≤ lsum εE23 3 - lrem εE23 3) := by decide +kernel

/-- Lowering the upper end of the E1 enclosure by one unit breaks it too. -/
theorem ctl_theta2_hi :
    ¬ (lsum εE23 3 + lrem εE23 3 ≤ (437127524 / 10 ^ 19 : ℚ) * (940648264778 / 10 ^ 11)) := by decide +kernel

/-- A centre of 2-subsets fails on 7-sets: `C(2,2)` is odd at the non-neighbour size `n = 2`. -/
theorem ctl_centre2 : ¬ (∀ n ∈ Finset.range 7, n % 3 ≠ 0 → Nat.choose n 2 % 2 = 0) := by decide

/-- X1's 4-subset centre (`|P| ≤ 2`) fails on 7-sets: `1 + 4 + C(4,2) = 11` is odd at the non-neighbour `n = 4`. -/
theorem ctl_centre_le2_on7 : ¬ (∀ n ∈ Finset.range 7, n % 3 ≠ 0 → (1 + n + Nat.choose n 2) % 2 = 0) := by decide

/-- The 3-subset centre needs `J`: `C(3,3) = 1` is odd at the neighbour size `n = 3`. -/
theorem ctl_noJ_E1 : ¬ (∀ n ∈ Finset.range 7, Nat.choose n 3 % 2 = 0) := by decide

end Mob
