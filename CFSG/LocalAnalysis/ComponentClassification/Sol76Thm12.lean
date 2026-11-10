module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank


@[expose] def AschbacherRankOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ∀ K : Subgroup G, IsSolomonMaximal K → CFSG.pRank 2 ↥K ≤ 1 →
      Blueprint.OddLieType (GeneralizedFitting.subgroup G)


end CFSG.ComponentClassification.Sol76
