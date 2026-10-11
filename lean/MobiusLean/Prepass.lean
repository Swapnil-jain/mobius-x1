import MobiusLean.Basic
import MobiusLean.DefsPrepass

/-!
# The numeric core of Theorems 1′ and 2 (PROOF.md §6 and §10, `x1_theorems.py`)

Both rows use the proved recursion of Thm 2.6′ (one directional step per kernel, roles padded to `W* = 3^w`) with
the two-sided pre-pass, so `μ = 2` and the saving per level is `Δ = 2 v² (v - 3 c h)`.

* **Theorem 1′** (4-subsets, Lucas centre `|P| ≤ 2`): `Δ₂ > 0` for every `h ∈ [43, 120]`, `Δ₂ < 0` for
  `h ∈ [4, 42]`; at `h = 51`, `W* = 3^46` and `1 - θ′ ∈ [4.22128277, 4.22128278]·10⁻¹³`.
* **Theorem 2** (E1: 7-subsets, centre `|P| = 3`, side wires on `|S ∩ T| = 3` only): `ΔE > 0` for every
  `h ∈ [20, 60]`, `ΔE < 0` for `h ∈ [7, 19]`; at `h = 23`, `W* = 3^45` and
  `1 - θ′ ∈ [4.37127524, 4.37127525]·10⁻¹¹`.

`θ` is defined once (`thetaOf m ε = log (m (1 - ε)) / log m`), and `one_sub_thetaOf_mem` turns two kernel-checked
rational inequalities into the enclosure of `1 - θ`.
-/

namespace Mob
open Real

/-! ## Ties to `Nat.choose` and the closed forms -/

lemma vE_eq_choose (h : ℕ) : vE h = Nat.choose h 7 := by
  rw [vE, Nat.choose_eq_descFactorial_div_factorial]; rfl

lemma cE_eq_choose (h : ℕ) : cE h = Nat.choose h 3 := by
  rw [cE, Nat.choose_eq_descFactorial_div_factorial]; rfl

lemma dE_eq_choose (h : ℕ) : dE h = 35 * Nat.choose (h - 7) 4 := by
  rw [dE, Nat.choose_eq_descFactorial_div_factorial]; rfl

/-- `Δ₂ = 2 v² (v - 3 c h)` (4-subsets, pre-pass). -/
lemma delta2_closed (h : ℕ) : Δ₂ h = 2 * (v h : ℤ) ^ 2 * (v h - 3 * c h * h) := by
  simp only [Δ₂, steps₂, N0, I0, Int.ofNat_eq_natCast]; push_cast; ring

/-- `ΔE = 2 v² (v - 3 c h)` (E1, pre-pass). -/
lemma deltaE_closed (h : ℕ) : ΔE h = 2 * (vE h : ℤ) ^ 2 * (vE h - 3 * cE h * h) := by
  simp only [ΔE, stepsE, N0E, I0E, Int.ofNat_eq_natCast]; push_cast; ring

/-! ## Sign thresholds -/

theorem delta2_pos_43_120 : ∀ h ∈ Finset.Icc 43 120, 0 < Δ₂ h := by decide +kernel
theorem delta2_neg_4_42 : ∀ h ∈ Finset.Icc 4 42, Δ₂ h < 0 := by decide +kernel
theorem deltaE_pos_20_60 : ∀ h ∈ Finset.Icc 20 60, 0 < ΔE h := by decide +kernel
theorem deltaE_neg_7_19 : ∀ h ∈ Finset.Icc 7 19, ΔE h < 0 := by decide +kernel

/-! ## Exact values at the chosen `h` -/

theorem consts_51 :
    v 51 = 249900 ∧ c 51 = 1327 ∧ d 51 = 178553 ∧ m 51 = 132651 ∧ W 51 = 8359663746785328810000 ∧
      Δ₂ 51 = 5853939037380000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem Wstar_51 : W 51 ≤ 3 ^ 46 ∧ 3 ^ 45 < W 51 := by constructor <;> decide +kernel

theorem constsE_23 :
    vE 23 = 245157 ∧ cE 23 = 1771 ∧ dE 23 = 63700 ∧ m 23 = 12167 ∧ WE 23 = 2815776474755079872223 ∧
      ΔE 23 = 14780032279463484 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem WstarE_23 : WE 23 ≤ 3 ^ 45 ∧ 3 ^ 44 < WE 23 := by constructor <;> decide +kernel

/-- The referee's spot values: `Δ₂` at `h = 49` and `ΔE` at `h = 21`. -/
theorem spot_values : Δ₂ 49 = 2841987244015808 ∧ ΔE 21 = 878597075232000 := by
  constructor <;> decide +kernel

/-! ## The exponent, for any level -/

/-- `θ = log (m (1 - ε)) / log m`: the exponent of a recursion with `λ = m (1 - ε)` (Thm 2.6′). -/
noncomputable def thetaOf (mm : ℕ) (ε : ℚ) : ℝ := log ((mm : ℝ) * (1 - (ε : ℝ))) / log (mm : ℝ)

lemma one_sub_thetaOf (mm : ℕ) (ε : ℚ) (hm : 1 < (mm : ℝ)) (hε : (ε : ℝ) < 1) :
    1 - thetaOf mm ε = -log (1 - (ε : ℝ)) / log (mm : ℝ) := by
  have mpos : (0 : ℝ) < mm := by linarith
  have lpos : 0 < log (mm : ℝ) := Real.log_pos hm
  have h1 : (0 : ℝ) < 1 - ε := by linarith
  unfold thetaOf
  rw [Real.log_mul mpos.ne' h1.ne', eq_div_iff lpos.ne', sub_mul, div_mul_cancel₀ _ lpos.ne']
  ring

lemma thetaOf_lt_one (mm : ℕ) (ε : ℚ) (hm : 1 < (mm : ℝ)) (h0 : (0 : ℝ) < ε) (h1 : (ε : ℝ) < 1) :
    thetaOf mm ε < 1 := by
  have mpos : (0 : ℝ) < mm := by linarith
  have hl : 0 < (mm : ℝ) * (1 - ε) := mul_pos mpos (by linarith)
  have hlm : (mm : ℝ) * (1 - ε) < mm := by nlinarith
  unfold thetaOf; rw [div_lt_one (Real.log_pos hm)]; exact Real.log_lt_log hl hlm

lemma thetaOf_pos (mm : ℕ) (ε : ℚ) (hm : 1 < (mm : ℝ)) (hl1 : 1 < (mm : ℝ) * (1 - ε)) : 0 < thetaOf mm ε :=
  div_pos (Real.log_pos hl1) (Real.log_pos hm)

/-- Enclosure of `1 - θ` from a log enclosure `a ≤ log m ≤ b` and two rational checks on the series of
`-log (1 - ε)` with `n` terms. -/
theorem one_sub_thetaOf_mem (mm : ℕ) (ε : ℚ) (n : ℕ) (a b lo hi : ℚ) (hm : 1 < (mm : ℝ)) (hε : |ε| < 1)
    (la : (a : ℝ) ≤ log (mm : ℝ)) (lb : log (mm : ℝ) ≤ b) (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi)
    (k1 : lo * b ≤ lsum ε n - lrem ε n) (k2 : lsum ε n + lrem ε n ≤ hi * a) :
    (lo : ℝ) ≤ 1 - thetaOf mm ε ∧ 1 - thetaOf mm ε ≤ hi := by
  have hε1 : (ε : ℝ) < 1 := by
    have := (abs_lt.mp hε).2; exact_mod_cast this
  rw [one_sub_thetaOf mm ε hm hε1]
  obtain ⟨A, B⟩ := log_one_sub_mem ε n hε
  have L0 : 0 < log (mm : ℝ) := Real.log_pos hm
  have k1' : ((lo : ℚ) : ℝ) * ((b : ℚ) : ℝ) ≤ ((lsum ε n : ℚ) : ℝ) - ((lrem ε n : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : ((lsum ε n : ℚ) : ℝ) + ((lrem ε n : ℚ) : ℝ) ≤ ((hi : ℚ) : ℝ) * ((a : ℚ) : ℝ) := by exact_mod_cast k2
  have lo0 : (0 : ℝ) ≤ lo := by exact_mod_cast hlo0
  have hi0 : (0 : ℝ) ≤ hi := by exact_mod_cast hhi0
  constructor
  · rw [le_div_iff₀ L0]; nlinarith [mul_le_mul_of_nonneg_left lb lo0]
  · rw [div_le_iff₀ L0]; nlinarith [mul_le_mul_of_nonneg_left la hi0]

/-! ## Theorem 1′: 4-subsets with the pre-pass, `h = 51`, `W* = 3^46` -/

def ε51 : ℚ := (Δ₂ 51 : ℚ) / ((3 : ℚ) ^ 46 * (m 51 : ℚ))

theorem eps51_bounds : (49792043455 / 10 ^ 22 : ℚ) < ε51 ∧ ε51 < 49792043456 / 10 ^ 22 := by
  constructor <;> decide +kernel

lemma m51_gt_one : 1 < ((m 51 : ℕ) : ℝ) := by rw [show m 51 = 132651 by decide +kernel]; norm_num

/-- `log 132651 ∈ [11.79547689817, 11.79547689818]` (`132651 = 2^17 (1 - t)`, `|t| ≈ 0.012`, 12 terms). -/
lemma log_m51_mem : ((1179547689817 / 10 ^ 11 : ℚ) : ℝ) ≤ log (m 51 : ℝ) ∧
    log (m 51 : ℝ) ≤ ((1179547689818 / 10 ^ 11 : ℚ) : ℝ) :=
  log_mem _ 132651 _ _ 17 12 _ _ (by rw [show m 51 = 132651 by decide +kernel]; norm_num) rfl rfl
    (by decide +kernel)

theorem theta1p_lt_one : thetaOf (m 51) ε51 < 1 := by
  have h0 : (0 : ℚ) < ε51 := lt_trans (by norm_num) eps51_bounds.1
  have h1 : ε51 < 1 := lt_trans eps51_bounds.2 (by norm_num)
  exact thetaOf_lt_one _ _ m51_gt_one (by exact_mod_cast h0) (by exact_mod_cast h1)

/-- **Theorem 1′: `1 - θ′ ∈ [4.22128277, 4.22128278]·10⁻¹³`.** -/
theorem one_sub_theta1p_bounds :
    ((422128277 / 10 ^ 21 : ℚ) : ℝ) ≤ 1 - thetaOf (m 51) ε51 ∧
      1 - thetaOf (m 51) ε51 ≤ ((422128278 / 10 ^ 21 : ℚ) : ℝ) := by
  have hε : |ε51| < 1 := by
    rw [abs_lt]; constructor
    · exact lt_trans (by norm_num : (-1 : ℚ) < 0) (lt_trans (by norm_num) eps51_bounds.1)
    · exact lt_trans eps51_bounds.2 (by norm_num)
  exact one_sub_thetaOf_mem (m 51) ε51 3 _ _ _ _ m51_gt_one hε log_m51_mem.1 log_m51_mem.2 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem theta1p_pos : 0 < thetaOf (m 51) ε51 := by
  have := one_sub_theta1p_bounds.2; push_cast at this; linarith

/-! ## Theorem 2: E1 with the pre-pass, `h = 23`, `W* = 3^45` -/

def εE23 : ℚ := (ΔE 23 : ℚ) / ((3 : ℚ) ^ 45 * (m 23 : ℚ))

theorem epsE23_bounds : (41118324737 / 10 ^ 20 : ℚ) < εE23 ∧ εE23 < 41118324738 / 10 ^ 20 := by
  constructor <;> decide +kernel

lemma m23_gt_one : 1 < ((m 23 : ℕ) : ℝ) := by rw [show m 23 = 12167 by decide +kernel]; norm_num

/-- `log 12167 ∈ [9.40648264778, 9.40648264779]` (`12167 = 2^14 (1 - t)`, `t ≈ 0.257`, 40 terms). -/
lemma log_m23_mem : ((940648264778 / 10 ^ 11 : ℚ) : ℝ) ≤ log (m 23 : ℝ) ∧
    log (m 23 : ℝ) ≤ ((940648264779 / 10 ^ 11 : ℚ) : ℝ) :=
  log_mem _ 12167 _ _ 14 40 _ _ (by rw [show m 23 = 12167 by decide +kernel]; norm_num) rfl rfl
    (by decide +kernel)

theorem theta2_lt_one : thetaOf (m 23) εE23 < 1 := by
  have h0 : (0 : ℚ) < εE23 := lt_trans (by norm_num) epsE23_bounds.1
  have h1 : εE23 < 1 := lt_trans epsE23_bounds.2 (by norm_num)
  exact thetaOf_lt_one _ _ m23_gt_one (by exact_mod_cast h0) (by exact_mod_cast h1)

/-- **Theorem 2: `1 - θ′ ∈ [4.37127524, 4.37127525]·10⁻¹¹`.** -/
theorem one_sub_theta2_bounds :
    ((437127524 / 10 ^ 19 : ℚ) : ℝ) ≤ 1 - thetaOf (m 23) εE23 ∧
      1 - thetaOf (m 23) εE23 ≤ ((437127525 / 10 ^ 19 : ℚ) : ℝ) := by
  have hε : |εE23| < 1 := by
    rw [abs_lt]; constructor
    · exact lt_trans (by norm_num : (-1 : ℚ) < 0) (lt_trans (by norm_num) epsE23_bounds.1)
    · exact lt_trans epsE23_bounds.2 (by norm_num)
  exact one_sub_thetaOf_mem (m 23) εE23 3 _ _ _ _ m23_gt_one hε log_m23_mem.1 log_m23_mem.2 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem theta2_pos : 0 < thetaOf (m 23) εE23 := by
  have := one_sub_theta2_bounds.2; push_cast at this; linarith

end Mob
