module

public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.Background.Harris.F112S3Big

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

@[expose] def F112B6Loc (L1 L2 : Subgroup G) : Prop :=
  IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 L1) ∧
    IsBlock2 L2 L2 ∧ IsL2Quot 2 (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 1 ∧ IsAltType L2 5


end CFSG.Quasithin.Background.Harris.F112S3Big
