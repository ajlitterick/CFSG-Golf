module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterCoefficients
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem blocksVChar_norm_one_signed_irreducible {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 1) :
    ∃ χ : BlocksIrr G, f = (χ : G → ℂ) ∨ f = -(χ : G → ℂ) := by
  obtain ⟨n, hn, _⟩ := blocksVChar_exists_unique_expansion hf
  have hsum : (∑ χ ∈ n.support, n χ ^ 2 : ℤ) = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_one, ← blocksInnerProduct_expansion_norm, hn]
    exact hnorm
  have hsum' : (∑ χ : n.support, n χ.val ^ 2 : ℤ) = 1 := by
    rwa [Finset.sum_subtype n.support (by intros; rfl)] at hsum
  obtain ⟨χ, hsign, houtside⟩ := integer_norm_one_single_coefficient
    (fun χ : n.support => n χ.val) hsum'
  have heq : f = (n χ.val : ℂ) • (χ.val : G → ℂ) := by
    rw [← hn]
    funext x
    rw [blocksCharacterExpansion_apply]
    change (∑ ψ ∈ n.support, (n ψ : ℂ) * (ψ : G → ℂ) x) = _
    rw [Finset.sum_eq_single χ.val]
    · rfl
    · intro ψ hψ hne
      have hzero : n ψ = 0 := houtside ⟨ψ, hψ⟩ (by
        intro hequal
        exact hne (congrArg Subtype.val hequal))
      rw [hzero, Int.cast_zero, zero_mul]
    · exact fun hnot => (hnot χ.property).elim
  refine ⟨χ.val, ?_⟩
  rcases hsign with hpos | hneg
  · exact Or.inl (by simpa only [hpos, Int.cast_one, one_smul] using heq)
  · exact Or.inr (by simpa only [hneg, Int.cast_neg, Int.cast_one, neg_one_smul] using heq)


end CFSG
