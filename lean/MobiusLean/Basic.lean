import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rigorous rational bounds on `Real.log`

Reused, with the namespace renamed, from the authors' own earlier Lean packages (the same file serves their other
kernel-checked numeric bounds). For `|t| < 1`, Mathlib's `Real.abs_log_sub_add_sum_range_le` bounds
`log (1 - t)` by a partial sum of its series; a positive rational `x` is written as `x = 2^k (1 - t)`, and
`log 2 = -log (1 - 1/2)` is bounded by the same series. Partial sums are computed in `ℚ` and compared by
`decide +kernel`. Nothing analytic is assumed.
-/

open Real Finset

namespace Mob

/-- `∑_{i<n} t^(i+1)/(i+1)` in `ℚ`, by recursion so that the kernel can evaluate it. -/
def lsum (t : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lsum t n + t ^ (n + 1) / ((n : ℚ) + 1)

/-- The tail bound `|t|^(n+1) / (1 - |t|)`. -/
def lrem (t : ℚ) (n : ℕ) : ℚ := |t| ^ (n + 1) / (1 - |t|)

lemma lsum_cast (t : ℚ) (n : ℕ) :
    ((lsum t n : ℚ) : ℝ) = ∑ i ∈ range n, (t : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
  induction n with
  | zero => simp [lsum]
  | succ n ih => rw [sum_range_succ, ← ih]; simp only [lsum]; push_cast; ring

lemma log_one_sub_mem (t : ℚ) (n : ℕ) (ht : |t| < 1) :
    -((lsum t n : ℚ) : ℝ) - ((lrem t n : ℚ) : ℝ) ≤ log (1 - (t : ℝ)) ∧
      log (1 - (t : ℝ)) ≤ -((lsum t n : ℚ) : ℝ) + ((lrem t n : ℚ) : ℝ) := by
  have ht' : |(t : ℝ)| < 1 := by rw [← Rat.cast_abs]; exact_mod_cast ht
  have h := Real.abs_log_sub_add_sum_range_le ht' n
  rw [← lsum_cast] at h
  have hr : ((lrem t n : ℚ) : ℝ) = |(t : ℝ)| ^ (n + 1) / (1 - |(t : ℝ)|) := by
    simp [lrem, Rat.cast_abs]
  rw [← hr] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- Rational bounds on `log 2`, from the series at `t = 1/2` with 150 terms (checked below). -/
def L2lo : ℚ := 693147180559945309417232121458176568075500134 / 10 ^ 45 - 1 / 10 ^ 42
def L2hi : ℚ := 693147180559945309417232121458176568075500134 / 10 ^ 45 + 1 / 10 ^ 42

lemma log_two_mem : (L2lo : ℝ) ≤ log 2 ∧ log 2 ≤ (L2hi : ℝ) := by
  have h := log_one_sub_mem (1 / 2) 150 (by norm_num [abs_of_pos])
  have e : log (2 : ℝ) = -log (1 - (((1 / 2 : ℚ)) : ℝ)) := by
    rw [show (1 : ℝ) - (((1 / 2 : ℚ)) : ℝ) = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  have c1 : L2lo ≤ lsum (1 / 2) 150 - lrem (1 / 2) 150 := by decide +kernel
  have c2 : lsum (1 / 2) 150 + lrem (1 / 2) 150 ≤ L2hi := by decide +kernel
  have c1' : (L2lo : ℝ) ≤ ((lsum (1 / 2) 150 : ℚ) : ℝ) - ((lrem (1 / 2) 150 : ℚ) : ℝ) := by
    exact_mod_cast c1
  have c2' : ((lsum (1 / 2) 150 : ℚ) : ℝ) + ((lrem (1 / 2) 150 : ℚ) : ℝ) ≤ (L2hi : ℝ) := by
    exact_mod_cast c2
  rw [e]; constructor <;> linarith [h.1, h.2]

lemma kmul_mem (k : ℤ) (a b l : ℝ) (ha : a ≤ l) (hb : l ≤ b) :
    min ((k : ℝ) * a) ((k : ℝ) * b) ≤ (k : ℝ) * l ∧ (k : ℝ) * l ≤ max ((k : ℝ) * a) ((k : ℝ) * b) := by
  rcases le_total 0 (k : ℝ) with hk | hk
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ha hk),
      (mul_le_mul_of_nonneg_left hb hk).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hb hk),
      (mul_le_mul_of_nonpos_left ha hk).trans (le_max_left _ _)⟩

/-- The kernel-checked condition behind `log_mem`: `x > 0`, `t = 1 - x/2^k` has `|t| < 1`, and the series
bound of `log x = log (1 - t) + k log 2` lies inside `[lo, hi]`. -/
def logOK (x : ℚ) (k : ℤ) (n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < x) && decide (|1 - x / 2 ^ k| < 1) &&
  decide (lo ≤ -(lsum (1 - x / 2 ^ k) n) - lrem (1 - x / 2 ^ k) n + min (k * L2lo) (k * L2hi)) &&
  decide (-(lsum (1 - x / 2 ^ k) n) + lrem (1 - x / 2 ^ k) n + max (k * L2lo) (k * L2hi) ≤ hi)

/-- Rigorous bounds `loR ≤ log e ≤ hiR` for a real expression `e` equal to the rational `x`. -/
theorem log_mem (e : ℝ) (x lo hi : ℚ) (k : ℤ) (n : ℕ) (loR hiR : ℝ) (he : e = x) (hlo : loR = lo)
    (hhi : hiR = hi) (h : logOK x k n lo hi = true) : loR ≤ log e ∧ log e ≤ hiR := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hx, ht⟩, h1⟩, h2⟩ := h
  have hb := log_one_sub_mem (1 - x / 2 ^ k) n ht
  have hy : (1 - (((1 - x / 2 ^ k : ℚ)) : ℝ)) = (x : ℝ) / 2 ^ k := by push_cast; ring
  rw [hy] at hb
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog : log (x : ℝ) = log ((x : ℝ) / 2 ^ k) + (k : ℝ) * log 2 := by
    rw [Real.log_div hxpos.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]; ring
  obtain ⟨l2a, l2b⟩ := log_two_mem
  have hk := kmul_mem k _ _ _ l2a l2b
  have h1' : ((lo : ℚ) : ℝ) ≤ ((-(lsum (1 - x / 2 ^ k) n) - lrem (1 - x / 2 ^ k) n
      + min (k * L2lo) (k * L2hi) : ℚ) : ℝ) := by exact_mod_cast h1
  have h2' : ((-(lsum (1 - x / 2 ^ k) n) + lrem (1 - x / 2 ^ k) n
      + max (k * L2lo) (k * L2hi) : ℚ) : ℝ) ≤ ((hi : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2'
  subst he hlo hhi
  rw [hlog]; constructor <;> linarith [hb.1, hb.2, hk.1, hk.2]

end Mob
