module

public import CFSG.ClassicalInvolution.AschTight.Thm6Tight3
public import CFSG.Goldschmidt75.CorollaryB3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem goldschmidtB3Tmp_holds : GoldschmidtB3Tmp :=
  fun G _ _ S A => CFSG.Goldschmidt75.goldschmidtB3 G S A


end CFSG.ClassicalInvolution.Disconnected.AschTight
