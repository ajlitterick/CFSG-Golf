module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.QuarticCharacter

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def pairDiagonal (left right : ℂ) : Module.End ℂ (ℂ × ℂ) where
  toFun vector := (left * vector.1, right * vector.2)
  map_add' := by intros; apply Prod.ext <;> simp [mul_add]
  map_smul' := by intros; apply Prod.ext <;> simp [smul_eq_mul, mul_left_comm]


end CFSG.TwoRankLowerBound.Helpers
