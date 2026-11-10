
module

public import CFSG.Monster.B.TwoA.Base.GeomObjBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

attribute [local instance] parAction


@[expose] def stdSub (J : Set ℕ) : Set ParGeom := {x | x ∈ stdParFlag ∧ parType x ∈ J}


end CFSG.Monster.B.TwoA
