module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR4Basic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms

section Lang

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def IsLangSurjective (α : MulAut X) : Prop :=
  ∀ z : X, α z = z⁻¹ → ∃ x : X, (α x)⁻¹ * x = z

theorem IsLangSurjective.of_mulEquiv (e : X ≃* Y) {α : MulAut X} {β : MulAut Y}
    (h : ∀ x, e (α x) = β (e x)) (hβ : IsLangSurjective β) : IsLangSurjective α := by
  intro z hz
  have hz' : β (e z) = (e z)⁻¹ := by rw [← h, hz, map_inv]
  obtain ⟨x, hx⟩ := hβ (e z) hz'
  refine ⟨e.symm x, e.injective ?_⟩
  rw [map_mul, map_inv, h, MulEquiv.apply_symm_apply, hx]

theorem IsLangSurjective.of_conj {α β ψ : MulAut X} (h : ψ * α * ψ⁻¹ = β)
    (hβ : IsLangSurjective β) : IsLangSurjective α :=
  IsLangSurjective.of_mulEquiv ψ (fun x => by
    rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply])
    hβ

end Lang

section Standard


end Standard

end CFSG.SeitzReduction.LinearPilot
