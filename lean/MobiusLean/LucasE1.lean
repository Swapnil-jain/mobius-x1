import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# The E1 centre over F₂ (PROOF.md §10, Lemma 10.1)

For finite sets `S`, `T` the E1 centre entry is `(RG)_{ST} = #{P ⊆ S ∩ T : |P| = 3} = C(n,3)` with `n = |S ∩ T|`
(`centre3_count`). Mod 2, `C(n,3)` is odd exactly at `n ∈ {3, 7}` for `n ≤ 7` (`centre3_table`). Hence for
7-subsets (`e1_gadget`): the diagonal is odd; distinct non-neighbours (`|S ∩ T| mod 3 ≠ 0`) are even; neighbours
with `|S ∩ T| ∈ {0, 6}` are even, so `J = RG` vanishes there and those pairs need no side wire; and the
neighbours with `|S ∩ T| = 3` are odd, so they are exactly the support of `J`.
-/

namespace Mob
open Finset

/-- `#{P ⊆ X : |P| = 3} = C(|X|, 3)`. -/
theorem centre3_count {α : Type*} [DecidableEq α] (X : Finset α) :
    (X.powerset.filter (fun P => P.card = 3)).card = X.card.choose 3 := by
  rw [← powersetCard_eq_filter, card_powersetCard]

/-- `C(n,3)` is odd exactly at `n = 3` and `n = 7`, for `n = 0, …, 7`. -/
theorem centre3_table : ∀ n ∈ Finset.range 8, (Nat.choose n 3 % 2 = 1 ↔ (n = 3 ∨ n = 7)) := by decide

/-- **Lemma 10.1.** For 7-subsets `S`, `T`, with `r = #{P ⊆ S ∩ T : |P| = 3} mod 2`. -/
theorem e1_gadget {α : Type*} [DecidableEq α] (S T : Finset α) (hS : S.card = 7) (hT : T.card = 7) :
    (S = T → ((S ∩ T).powerset.filter (fun P => P.card = 3)).card % 2 = 1) ∧
      (S ≠ T → (S ∩ T).card % 3 ≠ 0 → ((S ∩ T).powerset.filter (fun P => P.card = 3)).card % 2 = 0) ∧
      (S ≠ T → ((S ∩ T).card = 0 ∨ (S ∩ T).card = 6) →
        ((S ∩ T).powerset.filter (fun P => P.card = 3)).card % 2 = 0) ∧
      ((S ∩ T).card = 3 → ((S ∩ T).powerset.filter (fun P => P.card = 3)).card % 2 = 1) := by
  rw [centre3_count]
  have hle : (S ∩ T).card ≤ 7 := hS ▸ card_le_card inter_subset_left
  have h7 : S ≠ T → (S ∩ T).card ≠ 7 := by
    intro hne h7
    have e1 : S ∩ T = S := eq_of_subset_of_card_le inter_subset_left (by omega)
    have e2 : S ∩ T = T := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hne (e1.symm.trans e2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl; rw [inter_self, hS]; decide
  · intro hne hn
    have := h7 hne
    interval_cases h : (S ∩ T).card <;> first | decide | omega
  · intro _ hn
    rcases hn with hn | hn <;> rw [hn] <;> decide
  · intro hn; rw [hn]; decide

end Mob
