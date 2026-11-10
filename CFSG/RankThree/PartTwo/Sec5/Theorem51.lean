module

public import CFSG.RankThree.PartTwo.Sec5.Item57
public import CFSG.RankThree.PartTwo.Sec5.Item58

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank3II_5_1 {A S : Subgroup G} (h : SectionFiveHyp A S) :
    Statement51 A S := by
  induction hn : Nat.card S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  have ih' : ∀ S' : Subgroup G, S' < S → SectionFiveHyp A S' → Statement51 A S' :=
    fun S' hS' h' => ih (Nat.card S') (hn ▸ Subgroup.card_lt_of_lt hS') h' rfl
  rcases rank3II_5_6_of_ih h ih' with h2 | ⟨U, hU⟩
  · exact Or.inr h2
  · left
    have h58 := rank3II_5_8 h hU
    obtain ⟨hSA, hΩ⟩ := rank3II_5_7 h hU h58
    have hAS : A ⊓ Subgroup.centralizer (S : Set G) = A ⊓ Subgroup.centralizer (U : Set G) := by
      apply le_antisymm
      · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU.le))
      · refine le_inf inf_le_left ?_
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h58
    refine ⟨by rw [hAS]; exact card_inf_centralizer_fourGroup h hU, hSA, ?_, ?_⟩
    · rw [hΩ]
      exact hU.elemAbelian
    · rw [hΩ]
      exact hU.card_eq


end CFSG.RankThree.PartTwo.Sec5
