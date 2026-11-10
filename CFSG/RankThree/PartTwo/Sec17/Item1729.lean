module

public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly (InCatalog)

@[expose] def Item13Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ A ∈ partTwoF G, A ∉ partTwoT G →
      ∃ (c : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c


@[expose] def Item1728 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    ¬ Sec15R G A c L


end CFSG.RankThree.PartTwo.Sec17
