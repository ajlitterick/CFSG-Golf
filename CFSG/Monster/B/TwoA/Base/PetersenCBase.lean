
module

public import CFSG.Monster.B.TwoA.Base.PetersenB
public import CFSG.Monster.B.TwoA.Base.PetersenData
public import CFSG.Monster.B.TwoA.Base.Space34ABase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

@[expose] def aut4 (c : Fin 15) : AutPerm := ⟨perm4 c, perm4_mem c⟩

@[expose] def aut5 (d : Fin 10) : AutPerm := ⟨perm5 d, perm5_mem d⟩

theorem aut4_mem_Ppair (c : Fin 15) : aut4 c ∈ Ppair :=
  (mem_Ppair_iff _).2 (.inl ⟨perm4_fix c 0 (by decide), perm4_fix c 1 (by decide)⟩)

theorem aut5_mem_Ppair (d : Fin 10) : aut5 d ∈ Ppair :=
  (mem_Ppair_iff _).2 (.inl ⟨perm5_fix d 0 (by decide), perm5_fix d 1 (by decide)⟩)

@[expose] def UR4
    (c : Fin 15) : Submodule (ZMod 2) (Wv v0) :=
  U3.map (wAct v0 (kmon (aut4 c) (aut4_mem_Ppair c)))

@[expose] def UR5
    (d : Fin 10) : Submodule (ZMod 2) (Wv v0) :=
  U4.map (wAct v0 (kmon (aut5 d) (aut5_mem_Ppair d)))

@[expose] def Y4
    (c : Fin 15) : Subgroup Dfull := EU (UR4 c)

@[expose] def Y5
    (d : Fin 10) : Subgroup Dfull := EU (UR5 d)


end CFSG.Monster.B.TwoA
