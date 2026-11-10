module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.G92

open CFSG.Quasithin.G11
open scoped Matrix


private abbrev SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)


section Module


open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin


end Module

section Group


open CFSG.Quasithin.SzN31.CntLin


end Group


end CFSG.Quasithin.G92
