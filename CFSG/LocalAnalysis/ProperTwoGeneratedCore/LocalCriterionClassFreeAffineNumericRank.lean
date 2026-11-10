module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.Open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type*} [Group G] [Finite G]

theorem twoRank_le_one_of_not_twoRankAtLeastTwo
    (hrank : ¬ TwoRankAtLeastTwo G) : twoRank G ≤ 1 := by
  apply twoRank_le_one_of_no_four_group
  intro V hV hcard
  apply hrank
  refine ⟨V, hcard, ?_⟩
  intro v
  exact Subtype.ext (hV.2 v v.property)


end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
