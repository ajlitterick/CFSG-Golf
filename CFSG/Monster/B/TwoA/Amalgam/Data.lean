
module

public import CFSG.Monster.B.TwoA.Amalgam.DataBase

public import CFSG.Monster.B.TwoA.Par2.Class
public import CFSG.Monster.B.TwoA.Sp8.Par1Base
public import CFSG.Monster.B.TwoA.Sp8.QuadData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

@[expose] def Pc :
    Fin 4 → Subgroup Dfull := ![P1, Par2.H2, P3, P4]

@[expose] def Nc
    (i : Fin 4) : Subgroup Dfull := (CFSG.pCore 2 (Pc i)).map (Pc i).subtype

@[expose] def Eam :
    Subgroup Dfull := ⨆ i, Pc i

@[expose] def Bam :
    Subgroup Dfull := ⨅ i, Pc i

@[expose] def Qam
    (i : Fin 4) : Subgroup Dfull := ⨅ (j : Fin 4) (_ : j ≠ i), Pc j

theorem Pc_zero :
    Pc 0 = Jhat ⊓ Subgroup.centralizer {cQ} := rfl

theorem Pc_one :
    Pc 1 = Ntwo ⊓ Subgroup.centralizer {cQ} := rfl

theorem Pc_two :
    Pc 2 = K3 ⊓ Subgroup.centralizer {cQ} := rfl

theorem Pc_three :
    Pc 3 = Xgrp ⊓ Subgroup.centralizer {cQ} := rfl

theorem Pc_le_centralizer
    (i : Fin 4) : Pc i ≤ Subgroup.centralizer {cQ} := by
  fin_cases i <;> exact inf_le_right

theorem Eam_le_centralizer :
    Eam ≤ Subgroup.centralizer {cQ} := iSup_le Pc_le_centralizer

theorem Pc_le_Eam
    (i : Fin 4) : Pc i ≤ Eam := le_iSup Pc i

theorem Bam_le_Pc
    (i : Fin 4) : Bam ≤ Pc i := iInf_le Pc i

theorem Bam_le_Qam
    (i : Fin 4) : Bam ≤ Qam i := le_iInf₂ fun j _ => Bam_le_Pc j

theorem Qam_le_Pc
    {i j : Fin 4} (h : j ≠ i) : Qam i ≤ Pc j := iInf₂_le j h

theorem Pc_le_Shat
    (i : Fin 4) : Pc i ≤ Shat := by
  fin_cases i
  · exact inf_le_left.trans Jhat_le_Shat
  · exact inf_le_left.trans Ntwo_le_Shat
  · exact inf_le_left.trans K3_le_Shat
  · exact inf_le_left.trans Xgrp_le_Shat

theorem Eam_le_Shat :
    Eam ≤ Shat := iSup_le Pc_le_Shat


end CFSG.Monster.B.TwoA.Amalgam
