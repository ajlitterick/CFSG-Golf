
module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomStd
public import CFSG.Monster.B.TwoA.Sp8.SubgeomOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

attribute [local instance] parAction subgeomAction

attribute [local instance] parAction subgeomAction


theorem stdObj_mem_subgeom
    (i : ℕ) (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    stdObj i h1 (by omega) ∈ subgeom :=
  mem_subgeom.2 ⟨h4, 1, Xgrp.one_mem, (conjSub_one _).symm⟩


end CFSG.Monster.B.TwoA.Sp8
