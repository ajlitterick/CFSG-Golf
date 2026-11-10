module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def Covers (H X Y : Subgroup G) : Prop :=
  (X : Set G) ⊆ (H : Set G) * (Y : Set G)


theorem covers_iff {H X Y : Subgroup G} (hYX : Y ≤ X) (hXY : X ≤ normalizer (Y : Set G)) :
    Covers H X Y ↔ (H ⊓ X) ⊔ Y = X := by
  constructor
  · intro h
    apply le_antisymm (sup_le inf_le_right hYX)
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h hx
    have haX : a ∈ X := by
      have : a = a * b * b⁻¹ := by group
      rw [this]
      exact X.mul_mem hx (X.inv_mem (hYX hb))
    exact Subgroup.mul_mem_sup ⟨ha, haX⟩ hb
  · intro h x hx
    rw [← h] at hx
    have hle : H ⊓ X ≤ normalizer (Y : Set G) := inf_le_right.trans hXY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, ha.1, b, hb, rfl⟩


end CFSG.ABGLocalTools
