import MobiusLean.Numeric

/-! # Refuted controls for the numeric core: each perturbed statement is proved false by the kernel. -/

namespace Mob

/-- `3^54` is not enough roles: `W* = 3^55` is forced. -/
theorem ctl_Wstar_54 : ¬ (W 92 ≤ 3 ^ 54) := by decide +kernel

/-- The saving is negative at `h = 78`, so `h = 78` gives no exponent. -/
theorem ctl_delta_78 : ¬ (0 < Δ' 78) := by decide +kernel

/-- The stated `ε'` bounds are tight in the last digit. -/
theorem ctl_eps_lo : ¬ ((24837049274 / 10 ^ 24 : ℚ) < εq) := by decide +kernel
theorem ctl_eps_hi : ¬ (εq < 24837049273 / 10 ^ 24) := by decide +kernel

/-- Raising the lower end of the `1 - θ'` enclosure by one unit in the last digit breaks its rational check. -/
theorem ctl_theta_lo :
    ¬ ((1830916304 / 10 ^ 24 : ℚ) * (1356536573115 / 10 ^ 11) ≤ lsum εq 1 - lrem εq 1) := by
  decide +kernel

/-- The log enclosure of `m` fails when shifted by `10⁻¹¹`. -/
theorem ctl_log_m : logOK 778688 20 60 (1356536573115 / 10 ^ 11) (1356536573116 / 10 ^ 11) = false := by
  decide +kernel

end Mob
