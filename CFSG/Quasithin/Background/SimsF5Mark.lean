module

public import CFSG.Quasithin.Background.SimsF5Defs2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix CFSG.Open CFSG.Fischer CFSG.Fischer.Classification.Beta U42F431
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Pointwise

local instance (priority := high) mkDecEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)


section Transport


end Transport


section Subspaces


end Subspaces


section Cocycle


end Cocycle

section Parabolics


end Parabolics


end CFSG.Quasithin.SimsF5
