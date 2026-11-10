module

public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.PComponentCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.LocalBFailure

theorem pLayer_two_eq_twoLayer (G : Type*) [Group G] :
    CFSG.pLayer G 2 = TwoLayer.subgroup G := by
  unfold CFSG.pLayer TwoLayer.subgroup
  congr 1
  ext L
  exact CatalogueBAlternating.pComponent_two_iff L

theorem badSubgroup_eq_badTwoComponentSubgroup (G : Type*) [Group G] :
    TwoComponents.badSubgroup G = CatalogueBPrimeJoin.badTwoComponentSubgroup G := by
  unfold TwoComponents.badSubgroup CatalogueBPrimeJoin.badTwoComponentSubgroup
  congr 1
  ext L
  exact and_congr (CatalogueBAlternating.pComponent_two_iff L).symm
    (not_congr CatalogueBAlternating.quasisimple_iff_native.symm)


end CFSG.ComponentClassification.LocalBFailure
