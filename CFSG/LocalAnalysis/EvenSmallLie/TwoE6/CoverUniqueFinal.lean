module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUnique
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2DiagInput

public section

namespace CFSG.EvenSmallLie.TwoE6

theorem doubleCoverUnique
    : DoubleCoverUnique :=
  doubleCoverUnique_of_inputs leviA2DiagInput

theorem coverOuterLeTwo
    : CoverOuterLeTwo :=
  coverOuterLeTwo_of_inputs leviA2DiagInput

theorem child2E6_of_stroth
    (h21 : Stroth21) (h23 : Stroth23) : Child2E6 :=
  child2E6_of_inputs doubleCoverUnique coverOuterLeTwo h21 h23

end CFSG.EvenSmallLie.TwoE6
