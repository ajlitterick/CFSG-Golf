module

public import CFSG.CharacterTheory.Blocks.NormTwo

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem blocksInnerProduct_irreducible_principal {G : Type} [Group G] [Fintype G]
    (χ : BlocksIrr G) :
    BlocksInnerProduct (χ : G → ℂ) 1 = if (χ : G → ℂ) = 1 then 1 else 0 := by
  let principal : BlocksIrr G := ⟨1, by
    rw [blocksIrr_eq_irreducible_characters]
    exact ⟨principalFiniteComplexRepresentation G,
      principalFiniteComplexRepresentation_isIrreducible G,
      principalFiniteComplexRepresentation_character G⟩⟩
  simpa only [Subtype.ext_iff] using blocksInnerProduct_irreducible χ principal

theorem blocksVChar_degree_zero_norm_two_difference
    {G : Type} [Group G] [Fintype G] {f : G → ℂ}
    (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 2)
    (hdegree : f 1 = 0) :
    ∃ χ ψ : BlocksIrr G, χ ≠ ψ ∧
      (χ : G → ℂ) 1 = (ψ : G → ℂ) 1 ∧ f = (χ : G → ℂ) - (ψ : G → ℂ) := by
  obtain ⟨χ, ψ, ε, hne, hε, hequal, hexpansion⟩ :=
    blocksVChar_degree_zero_norm_two_signed_difference hf hnorm hdegree
  rcases hε with rfl | rfl
  · exact ⟨χ, ψ, hne, hequal, by
      simpa only [Int.cast_one, one_smul] using hexpansion⟩
  · exact ⟨ψ, χ, hne.symm, hequal.symm, by
      simpa only [Int.cast_neg, Int.cast_one, neg_one_smul, neg_sub_neg] using hexpansion⟩


end CFSG
