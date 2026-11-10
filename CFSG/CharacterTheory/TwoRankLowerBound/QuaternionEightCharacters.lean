module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionCyclicSection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers


@[expose] def scalarHomRepresentation {G : Type*} [Group G] (homomorphism : G →* ℂ) :
    Representation ℂ G ℂ where
  toFun element := homomorphism element • (1 : Module.End ℂ ℂ)
  map_one' := by simp
  map_mul' := by intros; simp [smul_smul, mul_comm]

theorem scalarHomRepresentation_character {G : Type*} [Group G]
    (homomorphism : G →* ℂ) :
    (scalarHomRepresentation homomorphism).character = homomorphism := by
  ext element
  change LinearMap.trace ℂ ℂ (homomorphism element • (1 : Module.End ℂ ℂ)) = _
  simp


end CFSG.TwoRankLowerBound.Helpers
