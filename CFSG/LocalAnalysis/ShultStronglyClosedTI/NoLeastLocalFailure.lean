module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ShultMilestoneAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerDischarge

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.ProperTwoGeneratedCore

theorem theoremTwo :
    Assembly.TheoremTwo :=
  HighRankPair.theoremTwo_of_unitaryMonomial UnitaryPairIndex.unitaryMonomialTheorem

theorem not_minimalInvolutionPointLocalFailure
    (G : Type) [Group G] [Finite G] (H : Subgroup G)
    (z : G) : ¬ MinimalInvolutionPointLocalFailure H z :=
  not_minimalLocalFailure_of_theoremTwo theoremTwo G H z


end CFSG.ShultStronglyClosedTI
