
module

public import CFSG.Monster.B.TwoA.Base.IncidenceBase
public import CFSG.Monster.B.TwoA.Base.GeomLin

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open scoped IsMulCommutative

attribute [local instance] parAction


@[expose] def stdChamber (g : Shat) : Set ParGeom := (g • ·) '' stdParFlag


end CFSG.Monster.B.TwoA
