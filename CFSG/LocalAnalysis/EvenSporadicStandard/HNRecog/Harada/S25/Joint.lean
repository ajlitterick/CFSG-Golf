module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts27
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Splus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

structure HaradaFactsAll (H : Type) [Group H] (E : Subgroup H) (a z b z₁ : H)
    (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) (zv : V6) (R0 F : Subgroup H) : Prop
    extends HaradaFacts27 H E a z b z₁ S T T' W0 ι zv R0 F,
      HaradaFacts3 H E a z b z₁ S T T' W0 ι where
  splus : SplusFact z

@[expose] def HaradaInterfaceAll : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∃ (a z b z₁ : H) (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) (zv : V6) (R0 F : Subgroup H),
      HaradaFactsAll H E a z b z₁ S T T' W0 ι zv R0 F


end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
