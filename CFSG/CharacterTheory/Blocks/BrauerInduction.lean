module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterRing
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators


theorem inducedFunction_mem_blocksVChar {G : Type} [Group G] [Fintype G]
    (E : Subgroup G) {φ : E → ℂ} (hφ : φ ∈ BlocksVChar E) :
    inducedFunction E φ ∈ BlocksVChar G := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hφ ⊢
  exact inducedFunction_mem_virtualCharacters E hφ


end CFSG
