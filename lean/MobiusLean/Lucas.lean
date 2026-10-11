import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# Lemma 1.2 (the Lucas centre) over F₂, and small-h brute-force checks

**General `h` (Finset proof).** For finite sets `S`, `T`, the centre matrix entry
`(RG)_{ST} = #{P ⊆ S ∩ T : |P| ≤ 2}` equals `1 + n + C(n,2)` with `n = |S ∩ T|` (`centre_count`). Mod 2 this is
`1, 0, 0, 1, 1` for `n = 0..4` (`lucas_table`). Hence for 4-subsets (`lucas_gadget`): `(RG)_{SS} ≡ 1`, and
`(RG)_{ST} ≡ 0` when `|S ∩ T| ∈ {1, 2}` (non-neighbours, `|S ∩ T| ≢ 0 mod 3`). Putting `J = RG` on neighbours gives
`RG + JV = I` over F₂, since `RG + RG = 0` there (this is `J = -RG` in characteristic 2).

The bitmask brute-force checks at small `h` are in `MobiusLean.Brute`.
-/

namespace Mob
open Finset

lemma filter_card_le_two {α : Type*} [DecidableEq α] (X : Finset α) :
    X.powerset.filter (fun P => P.card ≤ 2) =
      X.powersetCard 0 ∪ X.powersetCard 1 ∪ X.powersetCard 2 := by
  ext P; simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
  by_cases hP : P ⊆ X <;> simp only [hP, true_and, false_and, or_false] <;> omega

/-- `#{P ⊆ X : |P| ≤ 2} = 1 + |X| + C(|X|, 2)`. -/
theorem centre_count {α : Type*} [DecidableEq α] (X : Finset α) :
    (X.powerset.filter (fun P => P.card ≤ 2)).card = 1 + X.card + X.card.choose 2 := by
  rw [filter_card_le_two]
  have d01 : Disjoint (X.powersetCard 0) (X.powersetCard 1) :=
    disjoint_left.2 fun P h0 h1 => by
      rw [mem_powersetCard] at h0 h1; omega
  have d2 : Disjoint (X.powersetCard 0 ∪ X.powersetCard 1) (X.powersetCard 2) :=
    disjoint_left.2 fun P h h2 => by
      rw [mem_union, mem_powersetCard, mem_powersetCard] at h
      rw [mem_powersetCard] at h2; omega
  rw [card_union_of_disjoint d2, card_union_of_disjoint d01, card_powersetCard, card_powersetCard,
    card_powersetCard, Nat.choose_zero_right, Nat.choose_one_right]

/-- The Lucas table mod 2: `1 + n + C(n,2) ≡ 1, 0, 0, 1, 1` for `n = 0, …, 4`. -/
theorem lucas_table :
    (1 + 0 + Nat.choose 0 2) % 2 = 1 ∧ (1 + 1 + Nat.choose 1 2) % 2 = 0 ∧
      (1 + 2 + Nat.choose 2 2) % 2 = 0 ∧ (1 + 3 + Nat.choose 3 2) % 2 = 1 ∧
      (1 + 4 + Nat.choose 4 2) % 2 = 1 := by decide

/-- **Lemma 1.2 for every `h`.** For 4-subsets `S`, `T` of any finite type: the diagonal entry of `RG` is odd,
and the entry for distinct non-neighbours (`|S ∩ T| mod 3 ≠ 0`) is even. -/
theorem lucas_gadget {α : Type*} [DecidableEq α] (S T : Finset α) (hS : S.card = 4) (hT : T.card = 4) :
    (S = T → ((S ∩ T).powerset.filter (fun P => P.card ≤ 2)).card % 2 = 1) ∧
      (S ≠ T → (S ∩ T).card % 3 ≠ 0 → ((S ∩ T).powerset.filter (fun P => P.card ≤ 2)).card % 2 = 0) := by
  rw [centre_count]
  have hle : (S ∩ T).card ≤ 4 := hS ▸ card_le_card inter_subset_left
  constructor
  · rintro rfl; rw [inter_self, hS]; decide
  · intro hne hn
    have h4 : (S ∩ T).card ≠ 4 := by
      intro h4
      have e1 : S ∩ T = S := eq_of_subset_of_card_le inter_subset_left (by omega)
      have e2 : S ∩ T = T := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact hne (e1.symm.trans e2)
    interval_cases h : (S ∩ T).card <;> simp_all

end Mob
