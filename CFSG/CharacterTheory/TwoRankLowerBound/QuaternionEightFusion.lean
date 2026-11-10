module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.FocalFusion

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers


theorem orderOf_eq_of_isConj {G : Type*} [Group G] {left right : G}
    (hconjugate : IsConj left right) : orderOf left = orderOf right := by
  obtain ⟨conjugator, rfl⟩ := isConj_iff.mp hconjugate
  exact ((MulAut.conj conjugator).orderOf_eq left).symm


end CFSG.TwoRankLowerBound.Helpers
