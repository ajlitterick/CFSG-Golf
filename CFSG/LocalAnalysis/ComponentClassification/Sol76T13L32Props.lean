module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Close
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13BalancedProps

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem lemma32InputFor_simple_of_twoPart (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) : Lemma32InputFor simpleAmbient :=
  lemma32InputFor_of_twoPart hq (fun _ _ _ hG => kStarKProper_of_simpleAmbient hG) hR1
    fun _ _ _ hG _ hN' => not_le_solomonKStarOf_top_of_simple hG hN'


end CFSG.ComponentClassification.Sol76T13
