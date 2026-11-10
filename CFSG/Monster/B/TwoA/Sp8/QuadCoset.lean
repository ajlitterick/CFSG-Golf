
module

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetBase

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetC
public import CFSG.Monster.B.TwoA.Sp8.Normalizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371

theorem Lgrp_conj_Psi
    {l : Dfull} (hl : l ∈ Lgrp) (v : Fin 8 → ZMod 2) :
    l * Psi v * l⁻¹ = Psi v := by
  have h : Psi v * l = l * Psi v := Subgroup.mem_centralizer_iff.1 hl (Psi v) (Psi_mem_A8 v)
  rw [← h, mul_inv_cancel_right]

theorem Lgrp_conj_cQ
    {l : Dfull} (hl : l ∈ Lgrp) : l * cQ * l⁻¹ = cQ := by
  have hX := Lgrp_le_Xgrp hl
  obtain ⟨t, ht, -⟩ := (Xgrp_le_qPresGrp hX).2 0
  rw [Psi_zero', mul_one] at ht
  have hq : ∀ v, qPoly (t + v) = qPoly v := by
    intro v
    have e : l * (cQ * Psi v) * l⁻¹ = cQ * Psi (t + v) := by
      rw [show l * (cQ * Psi v) * l⁻¹ = (l * cQ * l⁻¹) * (l * Psi v * l⁻¹) by group, ht,
        Lgrp_conj_Psi hl, mul_assoc, ← Psi_add]
    exact qPoly_conj hX e
  have hqt : qPoly t = 0 := by
    have h := hq 0
    rwa [add_zero, qPoly_zero] at h
  have h0 : t = 0 := nondegenerate_b0.1 t fun v => by
    rw [b0_eq_qPoly, hq v, hqt, sub_zero, sub_self]
  rw [ht, h0, Psi_zero', mul_one]

theorem Lgrp_le_centralizer_T9 :
    Lgrp ≤ Subgroup.centralizer (T9 : Set Dfull) := by
  intro l hl
  rw [T9, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro x (rfl | hx)
  · have h := Lgrp_conj_cQ hl
    calc cQ * l = l * cQ * l⁻¹ * l := by rw [h]
      _ = l * cQ := by group
  · exact Subgroup.mem_centralizer_iff.1 hl x hx

theorem T9_le_Lgrp :
    T9 ≤ Lgrp := by
  rw [T9, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact cQ_mem_centralizer_A8
  · exact A8_le_Lgrp hx

theorem T9_le_center_Lgrp :
    T9.subgroupOf Lgrp ≤ Subgroup.center Lgrp := by
  intro t ht
  rw [Subgroup.mem_subgroupOf] at ht
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 l.2)) t ht).symm


end CFSG.Monster.B.TwoA.Sp8
