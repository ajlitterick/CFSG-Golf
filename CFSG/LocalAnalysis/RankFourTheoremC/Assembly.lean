module

public import CFSG.LocalAnalysis.RankFourTheoremC.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem uniqueFour_of_atCore (hpre : GLBPreuniqueness G) (hD1 : D1For G)
    (hE1 : AlmostStrongAtCore G) (hE2 : ConfinementAtCore G) : GLBUniqueFour G :=
  glbUniqueFour_iff.mpr ⟨almostStrongMaximalLocals_of_atCore hpre hD1 hE1,
    rankTwoConfinement_of_atCore hpre hD1 hE2⟩


end CFSG.LocalAnalysis.RankFourTheoremC
