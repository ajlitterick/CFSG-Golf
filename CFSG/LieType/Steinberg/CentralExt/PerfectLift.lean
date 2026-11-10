module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

universe u v w

section Generic

variable {H : Type u} {E : Type v} {G : Type*} [Group H] [Group E] [Group G] {π : E →* G}

theorem eq_of_comp_eq_of_isPerfect [Group.IsPerfect H] (hcen : π.ker ≤ Subgroup.center E)
    {β₁ β₂ : H →* E} (h : π.comp β₁ = π.comp β₂) : β₁ = β₂ := by
  have hmem : ∀ x, β₁ x * (β₂ x)⁻¹ ∈ Subgroup.center E := fun x => hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply,
      mul_inv_cancel])
  let γ : H →* Subgroup.center E :=
    { toFun := fun x => ⟨β₁ x * (β₂ x)⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.1 (hmem y)
        change β₁ (x * y) * (β₂ (x * y))⁻¹ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc β₁ x * β₁ y * ((β₂ y)⁻¹ * (β₂ x)⁻¹)
            = β₁ x * ((β₁ y * (β₂ y)⁻¹) * (β₂ x)⁻¹) := by group
          _ = β₁ x * ((β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)) := by rw [← hc]
          _ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹) := by group) }
  have hγ : ∀ x, γ x = 1 := by
    intro x
    have hx : x ∈ commutator H := by
      rw [Group.IsPerfect.commutator_eq_top]
      trivial
    exact Abelianization.commutator_subset_ker γ hx
  ext x
  have := congrArg Subtype.val (hγ x)
  simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
  exact mul_inv_eq_one.1 this

open _root_.Classical in
noncomputable def perfectLift (π : E →* G) (α : H →* G) : H →* E :=
  if h : ∃ β : H →* E, π.comp β = α then h.choose else 1

theorem comp_perfectLift_of_exists {α : H →* G} (h : ∃ β : H →* E, π.comp β = α) :
    π.comp (perfectLift π α) = α := by
  classical
  rw [perfectLift, dite_eq_left h]
  exact h.choose_spec


end Generic

section Extension


end Extension

end CFSG.LieType.Steinberg
