module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def UMovesCond (Y : Type) [Group Y] : Prop :=
  ∀ u : Y, orderOf u = 2 → ∀ α : MulAut Y, α * α = 1 → ∃ h : Y, α (h * u * h⁻¹) = h * u * h⁻¹

theorem UMovesCond.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : UMovesCond Y) : UMovesCond Y' := by
  intro u hu α hα
  let φ : MulAut Y' → MulAut Y := fun a => (e.trans a).trans e.symm
  have hφ : ∀ (a : MulAut Y') (y : Y), φ a y = e.symm (a (e y)) := fun a y => rfl
  have hmul : ∀ a b : MulAut Y', φ (a * b) = φ a * φ b := fun a b => MulEquiv.ext fun y => by
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply, hφ, hφ, MulEquiv.apply_symm_apply]
  have hone : φ 1 = 1 := MulEquiv.ext fun y => by
    rw [hφ, MulAut.one_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  have hu' : orderOf (e.symm u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
  obtain ⟨x, hx⟩ := h (e.symm u) hu' (φ α) (by rw [← hmul, hα, hone])
  refine ⟨e x, ?_⟩
  rw [hφ] at hx
  have := congrArg e hx
  simpa [map_mul, map_inv] using this


end CFSG.EvenSporadicStandard.Solomon78
