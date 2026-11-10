module

public import CFSG.CharacterTheory.Blocks.NormTwoNonprincipal
public import CFSG.CharacterTheory.Blocks.NormTwoConnector

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem blocksInnerProduct_irreducible_differences
    {G : Type} [Group G] [Fintype G] (a b c d : BlocksIrr G) :
    BlocksInnerProduct ((a : G → ℂ) - (b : G → ℂ))
        ((c : G → ℂ) - (d : G → ℂ)) =
      (if a = c then (1 : ℂ) else 0) - (if a = d then 1 else 0) -
        (if b = c then 1 else 0) + (if b = d then 1 else 0) := by
  have hp (x y : BlocksIrr G) : characterPairing (x : G → ℂ) (y : G → ℂ) =
      if x = y then 1 else 0 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure y.property)]
    exact blocksInnerProduct_irreducible x y
  rw [blocksInnerProduct_eq_characterPairing _ ((BlocksVChar G).sub_mem
    (AddSubgroup.subset_closure c.property) (AddSubgroup.subset_closure d.property)),
    characterPairing_sub_left, characterPairing_sub_right, characterPairing_sub_right,
    hp, hp, hp, hp]
  ring

theorem blocksIrr_differences_share_of_pairing_one
    {G : Type} [Group G] [Fintype G] (a b c d : BlocksIrr G)
    (hpair : BlocksInnerProduct ((a : G → ℂ) - (b : G → ℂ))
      ((c : G → ℂ) - (d : G → ℂ)) = 1) : a = c ∨ b = d := by
  by_cases hac : a = c
  · exact Or.inl hac
  by_cases hbd : b = d
  · exact Or.inr hbd
  rw [blocksInnerProduct_irreducible_differences] at hpair
  simp only [hac, hbd, ↓reduceIte, zero_sub, add_zero] at hpair
  split_ifs at hpair <;> norm_num at hpair

theorem pairwise_shared_pairs_have_common_coordinate
    {index label : Type*} [Nonempty index] (a b : index → label)
    (hshare : ∀ i j, i ≠ j → a i = a j ∨ b i = b j) :
    (∃ common, ∀ i, a i = common) ∨ (∃ common, ∀ i, b i = common) := by
  classical
  let base : index := Classical.arbitrary index
  by_cases ha : ∀ i, a i = a base
  · exact Or.inl ⟨a base, ha⟩
  obtain ⟨other, hother⟩ := not_forall.mp ha
  have hotherne : other ≠ base := by
    intro h
    exact hother (congrArg a h)
  have hb : b other = b base :=
    (hshare other base hotherne).resolve_left hother
  refine Or.inr ⟨b base, ?_⟩
  intro i
  by_cases hi : i = base
  · exact congrArg b hi
  by_cases hbi : b i = b base
  · exact hbi
  have hai : a i = a base := (hshare i base hi).resolve_right hbi
  have hione : i ≠ other := by
    intro h
    exact hother ((congrArg a h).symm.trans hai)
  rcases hshare i other hione with heq | heq
  · exact (hother (heq.symm.trans hai)).elim
  · exact heq.trans hb


end CFSG
