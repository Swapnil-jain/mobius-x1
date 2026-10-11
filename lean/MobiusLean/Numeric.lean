import MobiusLean.Basic
import MobiusLean.Defs

/-!
# The numeric core of X1 (PROOF.md §7, `x1/x1_exponent_count.py`)

Parameters of the genuine instance at label size `h` (4-subsets of `[h]`, Lucas centre):

* `v h = C(h,4)` label vectors per factor, `c h = 1 + h + C(h,2)` centre wires,
* `d h = C(h-4,4) + 4 (h-4)` ordered neighbours of one 4-subset (`|S ∩ T| ∈ {0,3}`),
* `m h = h^3`, `N₀ = v³`, `I₀ = 3 v²`, `W = 2 N₀ + 3 v² (v d + c)` roles,
* the step count `s' = W m - N₀ + 2 I₀ c h` (Lemma 2.3′), and the saving `Δ' = W m - s'`.

The binomials are written as falling products over `24` and `2` (in `MobiusLean.Defs`, which imports no Mathlib) so that
the kernel evaluates them quickly;
`v_eq_choose`, `c_eq_choose` and `d_eq_choose` tie them to `Nat.choose`. The formula for `d` is checked
against brute-force enumeration in `MobiusLean.Lucas` (small `h`) and by enumeration in Python at h = 92.

What is proved here: the exact values at h = 92, `W ≤ 3^55 < 3 W` (so `W* = 3^55` is the least power of 3
that is at least `W`), `Δ' > 0` for every `h` in `[79, 92]`, `Δ' < 0` at `h = 78`, rational bounds on
`ε' = Δ'/(3^55 m)`, the chain `Δ' > 0 → ε' > 0 → λ' = m (1 - ε') < m → θ' = log λ' / log m < 1`, and the
enclosure `1.830916303e-15 ≤ 1 - θ' ≤ 1.830916304e-15`.
-/

namespace Mob
open Real

lemma v_eq_choose (h : ℕ) : v h = Nat.choose h 4 := by
  rw [v, Nat.choose_eq_descFactorial_div_factorial]; rfl

lemma c_eq_choose (h : ℕ) : c h = 1 + h + Nat.choose h 2 := by
  rw [c, Nat.choose_eq_descFactorial_div_factorial]; rfl

lemma d_eq_choose (h : ℕ) : d h = Nat.choose (h - 4) 4 + 4 * (h - 4) := by
  rw [d, Nat.choose_eq_descFactorial_div_factorial]; rfl

/-- `Δ' = v² (v - 6 c h)`, the closed form of PROOF.md §7. -/
lemma delta_closed (h : ℕ) : Δ' h = (v h : ℤ) ^ 2 * (v h - 6 * c h * h) := by
  simp only [Δ', steps, N0, I0, Int.ofNat_eq_natCast]; push_cast; ring

theorem consts_92 :
    v 92 = 2794155 ∧ c 92 = 4279 ∧ d 92 = 2332242 ∧ m 92 = 778688 ∧
      W 92 = 152632308680970042196469925 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `W* = 3^55`: the least power of 3 that is `≥ W` at h = 92. -/
theorem Wstar_92 : W 92 ≤ 3 ^ 55 ∧ 3 ^ 54 < W 92 := by
  constructor <;> decide +kernel

theorem delta_92 : Δ' 92 = 3373902208276911675 := by decide +kernel

theorem delta_pos_79_92 : ∀ h ∈ Finset.Icc 79 92, 0 < Δ' h := by decide +kernel

theorem delta_neg_78 : Δ' 78 < 0 := by decide +kernel

/-- `ε' = Δ' / (W* m)` at h = 92, as a rational. -/
def εq : ℚ := (Δ' 92 : ℚ) / ((3 : ℚ) ^ 55 * (m 92 : ℚ))

theorem eps_bounds : (24837049273 / 10 ^ 24 : ℚ) < εq ∧ εq < 24837049274 / 10 ^ 24 := by
  constructor <;> decide +kernel

/-- `λ' = m (1 - ε')` and `θ' = log λ' / log m` (Thm 2.6′). -/
noncomputable def lam : ℝ := (m 92 : ℝ) * (1 - (εq : ℝ))
noncomputable def θ' : ℝ := log lam / log (m 92 : ℝ)

/-- Rational enclosure of `log m` at h = 92 (`m = 778688 = 2^20 (1 - t)`, t ≈ 0.257, 60 series terms). -/
lemma log_m_mem : ((1356536573114 / 10 ^ 11 : ℚ) : ℝ) ≤ log (m 92 : ℝ) ∧
    log (m 92 : ℝ) ≤ ((1356536573115 / 10 ^ 11 : ℚ) : ℝ) :=
  log_mem _ 778688 _ _ 20 60 _ _ (by rw [show m 92 = 778688 by decide +kernel]; norm_num) rfl rfl
    (by decide +kernel)

lemma eps_pos : (0 : ℝ) < εq := by
  have := eps_bounds.1; have h0 : (0 : ℚ) < εq := lt_trans (by norm_num) this; exact_mod_cast h0

lemma eps_lt_one : (εq : ℝ) < 1 := by
  have := eps_bounds.2; have h0 : εq < 1 := lt_trans this (by norm_num); exact_mod_cast h0

lemma m_pos : (0 : ℝ) < (m 92 : ℝ) := by
  rw [show m 92 = 778688 by decide +kernel]; norm_num

lemma log_m_pos : 0 < log (m 92 : ℝ) := lt_of_lt_of_le (by norm_num) log_m_mem.1

/-- The chain to `θ' < 1`: `Δ' > 0` gives `ε' > 0`, so `λ' < m`, so `log λ' < log m`. -/
theorem theta_lt_one : θ' < 1 := by
  have hl : 0 < lam := mul_pos m_pos (by linarith [eps_lt_one])
  have hlm : lam < (m 92 : ℝ) := by
    unfold lam; nlinarith [eps_pos, m_pos]
  have := Real.log_lt_log hl hlm
  unfold θ'; rw [div_lt_one log_m_pos]; exact this

theorem theta_pos : 0 < θ' := by
  have hl1 : 1 < lam := by
    unfold lam; rw [show m 92 = 778688 by decide +kernel]
    have := eps_bounds.2
    have h1 : (εq : ℝ) < ((24837049274 / 10 ^ 24 : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at h1 ⊢; nlinarith
  exact div_pos (Real.log_pos hl1) log_m_pos

/-- `1 - θ' = -log (1 - ε') / log m`. -/
lemma one_sub_theta : 1 - θ' = -log (1 - (εq : ℝ)) / log (m 92 : ℝ) := by
  have h1 : (0 : ℝ) < 1 - εq := by linarith [eps_lt_one]
  unfold θ' lam
  rw [Real.log_mul m_pos.ne' h1.ne', eq_div_iff log_m_pos.ne', sub_mul, div_mul_cancel₀ _ log_m_pos.ne']
  ring

/-- **`1 - θ' ∈ [1.830916303e-15, 1.830916304e-15]`** at h = 92, W* = 3^55. -/
theorem one_sub_theta_bounds :
    ((1830916303 / 10 ^ 24 : ℚ) : ℝ) ≤ 1 - θ' ∧ 1 - θ' ≤ ((1830916304 / 10 ^ 24 : ℚ) : ℝ) := by
  rw [one_sub_theta]
  have hε : |εq| < 1 := by
    rw [abs_lt]; constructor
    · exact lt_trans (by norm_num : (-1 : ℚ) < 0)
        (lt_trans (by norm_num : (0 : ℚ) < 24837049273 / 10 ^ 24) eps_bounds.1)
    · exact lt_trans eps_bounds.2 (by norm_num)
  obtain ⟨a, b⟩ := log_one_sub_mem εq 1 hε
  obtain ⟨la, lb⟩ := log_m_mem
  have lpos := log_m_pos
  -- rational facts, by the kernel
  have k1 : (1830916303 / 10 ^ 24 : ℚ) * (1356536573115 / 10 ^ 11) ≤ lsum εq 1 - lrem εq 1 := by
    decide +kernel
  have k2 : lsum εq 1 + lrem εq 1 ≤ (1830916304 / 10 ^ 24 : ℚ) * (1356536573114 / 10 ^ 11) := by
    decide +kernel
  have k1' : ((1830916303 / 10 ^ 24 : ℚ) : ℝ) * ((1356536573115 / 10 ^ 11 : ℚ) : ℝ) ≤
      ((lsum εq 1 : ℚ) : ℝ) - ((lrem εq 1 : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : ((lsum εq 1 : ℚ) : ℝ) + ((lrem εq 1 : ℚ) : ℝ) ≤
      ((1830916304 / 10 ^ 24 : ℚ) : ℝ) * ((1356536573114 / 10 ^ 11 : ℚ) : ℝ) := by exact_mod_cast k2
  have tlo : (0 : ℝ) ≤ ((1830916303 / 10 ^ 24 : ℚ) : ℝ) := by norm_num
  have thi : (0 : ℝ) ≤ ((1830916304 / 10 ^ 24 : ℚ) : ℝ) := by norm_num
  constructor
  · rw [le_div_iff₀ lpos]
    nlinarith [mul_le_mul_of_nonneg_left lb tlo]
  · rw [div_le_iff₀ lpos]
    nlinarith [mul_le_mul_of_nonneg_left la thi]

end Mob
