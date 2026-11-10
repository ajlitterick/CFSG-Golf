module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Balanced
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13ProductProps

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem kStarKProper_of_simpleAmbient {G : Type} [Group G] [Finite G] (hG : SimpleAmbient G) :
    KStarKProper G :=
  have := hG.1
  kStarKProper_of_simple hG.2.1 hG.2.2


end CFSG.ComponentClassification.Sol76T13
