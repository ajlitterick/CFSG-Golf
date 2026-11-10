module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Held
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.H13.FiveMenu

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial
open scoped MatrixGroups

theorem transvection15_eq_cornerTransvection :
    Quasithin.H13.transvection15 = DW.cornerTransvection (N := 5) (by norm_num) :=
  rfl


end CFSG.ComponentClassification.AS81
