module

public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents

public section

namespace CFSG.ComponentClassification.BFailureOdd

open CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem badSubgroup_eq_badTwoComponentSubgroup (X : Type*) [Group X] :
    TwoComponents.badSubgroup X = badTwoComponentSubgroup X := by
  unfold TwoComponents.badSubgroup badTwoComponentSubgroup
  congr 1
  ext L
  exact and_congr (CatalogueBAlternating.pComponent_two_iff L).symm
    (not_congr CatalogueBAlternating.quasisimple_iff_native.symm)


end CFSG.ComponentClassification.BFailureOdd
