
module


public import CFSG.Monster.B.TwoA.Sp8.GenActionImage

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA


theorem toAdd_ne_zero_of_ne_one
    {x : Dfull} (hx : x ∈ A8) (h1 : x ≠ 1) :
    Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩) ≠ 0 := by
  intro h
  apply h1
  have e : aEquiv (aEquiv.symm ⟨x, hx⟩) = ⟨x, hx⟩ := MulEquiv.apply_symm_apply _ _
  rw [← ofAdd_toAdd (aEquiv.symm ⟨x, hx⟩), h, ofAdd_zero, map_one] at e
  exact (congrArg Subtype.val e).symm

theorem coe_aEquiv_symm
    {x : Dfull} (hx : x ∈ A8) :
    (aEquiv (Multiplicative.ofAdd (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩))) : Dfull) = x := by
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem Xgrp_transitive
    {x y : Dfull} (hx : x ∈ A8) (hy : y ∈ A8) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : ∃ g ∈ Xgrp, g * x * g⁻¹ = y := by
  obtain ⟨f₁, hf₁, e₁⟩ := exists_conjImage_X (toAdd_ne_zero_of_ne_one hx hx1)
  obtain ⟨f₂, hf₂, e₂⟩ := exists_conjImage_X (toAdd_ne_zero_of_ne_one hy hy1)
  have hf : f₂ * f₁⁻¹ ∈ (Xgrp.subgroupOf NA8).map conjHom := by
    rw [conjImage_X]
    exact Subgroup.mul_mem _ hf₂ (Subgroup.inv_mem _ hf₁)
  obtain ⟨n, hn, hnf⟩ := hf
  refine ⟨n, Subgroup.mem_subgroupOf.1 hn, ?_⟩
  have hv : f₁⁻¹ (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩)) = Pi.single 0 1 := by
    rw [← e₁]
    exact f₁.symm_apply_apply _
  have hnv : conjHom n (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩)) =
      Multiplicative.toAdd (aEquiv.symm ⟨y, hy⟩) := by
    rw [hnf, LinearEquiv.mul_apply, hv, e₂]
  have h := aEquiv_conjHom n (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩))
  rw [hnv, coe_aEquiv_symm hy, coe_aEquiv_symm hx] at h
  exact h.symm


end CFSG.Monster.B.TwoA.Sp8
