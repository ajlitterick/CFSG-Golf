module

public import CFSG.RankThree.GF2n.Smith81.Sec216LocalLift

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def InCaseE3L (M Q Z B : Subgroup G) : Prop :=
  ∃ t : G, CtxD4 M Q Z B t ∧ CaseE3L M Q Z B

@[expose] def InCaseE4 (M Q Z B : Subgroup G) : Prop :=
  ∃ t : G, CtxD4 M Q Z B t ∧ CaseE4 M Q Z B t

@[expose] def InCaseE5 (M Q Z B : Subgroup G) : Prop :=
  ∃ t : G, CtxD4 M Q Z B t ∧ CaseE5 M Q Z B t


end CFSG.RankThree.GF2n.Smith81
