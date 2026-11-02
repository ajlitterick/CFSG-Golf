module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24OrdersCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

theorem sporadicCaseOdd_Fi24Prime
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .Fi24Prime := by
  obtain ⟨hP, hQ, hirr, hfaith, h4, hC⟩ := twoB_facts_checked
  exact sporadicCaseOdd_Fi24Prime_of_facts h32 h33 transpositionOrderFour twoAOrderFour
    twoACentralizer hP hQ hirr hfaith h4 hC

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
