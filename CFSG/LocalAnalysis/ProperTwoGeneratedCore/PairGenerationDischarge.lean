module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairGenerationTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoRemaining

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.Assembly

theorem pairCommutatorGenerationTheorem
    (G : Type) [Group G] [Finite G] :
    RankOnePair.PairCommutatorGenerationTheorem G := fun H z h _ hbeta _ ht => by
  rw [← minimalLocalFailureProperPairHull_eq_native]
  exact PairGeneration.pair_generated_hull_eq_top G H z h hbeta ht


theorem linearSuzukiHullOddCoreTrivial_holds
    (G : Type) [Group G] [Finite G] :
    LinearSuzukiHullOddCoreTrivial G :=
  linearSuzukiHullOddCoreTrivial (pairCommutatorGenerationTheorem G)


theorem theoremTwo_of_solvable_and_monomial
    (h : ∀ (G : Type) [Group G] [Finite G],
      SolvableLinearCosetNormalizerTheorem G ∧ UnitaryMonomialTheorem G) : TheoremTwo :=
  theoremTwo_of_generation fun G _ _ => ⟨pairCommutatorGenerationTheorem G, (h G).1, (h G).2⟩


end CFSG.ProperTwoGeneratedCore.HighRankPair
