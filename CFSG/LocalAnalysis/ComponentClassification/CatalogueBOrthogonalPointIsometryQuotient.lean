module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryPoints
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionProjective

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CatalogueBOrthogonalPointAction

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {R : QuadraticForm K W}

theorem mem_scalarKernel_isometry_iff (e : Q.IsometryEquiv R) (g : elementaryGroup Q) :
    elementaryIsometryEquiv e g ∈ scalarKernel R ↔ g ∈ scalarKernel Q := by
  rw [mem_scalarKernel_iff_units R, mem_scalarKernel_iff_units Q]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun x => ?_⟩
    have h := ha (e x)
    change (elementaryIsometryEquiv e g).val (e x) = (a : K) • e x at h
    rw [elementaryIsometryEquiv_apply, e.symm_apply_apply] at h
    apply e.injective
    change e (g.val x) = e ((a : K) • x)
    rw [map_smul]
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun x => ?_⟩
    rw [elementaryIsometryEquiv_apply, ha, map_smul, e.apply_symm_apply]


end CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
