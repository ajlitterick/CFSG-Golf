module

public import CFSG.YGroups.Y443.TerminalOrder
public import CFSG.YGroups.Y443.Native.EdgeNoncomm
public import CFSG.YGroups.Y443.Native.AlignCgen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Open (MonsterY443Derived)
open CFSG.YGroups.Y443Edge

theorem fM_C_ne_one :
    fM y443C ≠ 1 := by
  intro h
  apply fM_y443C_ne_one
  rw [h]
  rfl

theorem axElt_U11_mem_H :
    axElt y443U11 ∈ y443H := by
  have e : axElt y443U11 = y443T none * y443T (some y443U11) :=
    Subtype.ext (y443T_mul_coe none (some y443U11)).symm
  rw [e]
  exact y443H.mul_mem (y443T_mem_H (by decide)) (y443T_mem_H (by decide))

theorem fM_terminal_order
    : Q343N ≤ Nat.card (y443H.map fM) :=
  terminal_order fM fM_C_ne_one ⟨fM (axElt y443U11), ⟨_, axElt_U11_mem_H, rfl⟩, orderOf_fM_b1⟩

theorem fM_injOn_H
    : Set.InjOn fM y443H := injOn_H fM fM_terminal_order


end CFSG.YGroups.Y443
