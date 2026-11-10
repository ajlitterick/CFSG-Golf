
module


public import CFSG.Monster.B.TwoA.Sp8.A8

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def Lgrp :
    Subgroup Dfull := Subgroup.centralizer (A8 : Set Dfull)

@[expose] def bA
    (x y : A8) : ZMod 2 :=
  b0 (Multiplicative.toAdd (aEquiv.symm x)) (Multiplicative.toAdd (aEquiv.symm y))


end CFSG.Monster.B.TwoA.Sp8
