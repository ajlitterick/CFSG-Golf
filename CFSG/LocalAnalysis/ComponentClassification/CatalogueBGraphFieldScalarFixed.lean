module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalar

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearInner CatalogueBUnitaryIsometry

universe u


@[expose] def scalarPSLInclusion (n : ℕ) (K : Type u) [Field K] :
    ScalarProjectiveSpecialLinear n K →* ScalarProjectiveGeneralLinear n K :=
  (scalarProjectiveGeneralLinearEquiv n K).symm.toMonoidHom.comp
    (ProjectiveSpecialLinearGroup.toPGL.comp (scalarProjectiveSpecialLinearEquiv n K).toMonoidHom)

theorem scalarPSLInclusion_native (n : ℕ) (K : Type u) [Field K]
    (x : ScalarProjectiveSpecialLinear n K) :
    scalarProjectiveGeneralLinearEquiv n K (scalarPSLInclusion n K x) =
      ProjectiveSpecialLinearGroup.toPGL (scalarProjectiveSpecialLinearEquiv n K x) :=
  (scalarProjectiveGeneralLinearEquiv n K).apply_symm_apply _


abbrev scalarPSLRange (n : ℕ) (K : Type u) [Field K] :
    Subgroup (ScalarProjectiveGeneralLinear n K) := (scalarPSLInclusion n K).range


theorem scalarPSLRange_eq_comap (n : ℕ) (K : Type u) [Field K] :
    scalarPSLRange n K = (pslRange n K).comap (scalarProjectiveGeneralLinearEquiv n K).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨scalarProjectiveSpecialLinearEquiv n K y, (scalarPSLInclusion_native n K y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(scalarProjectiveSpecialLinearEquiv n K).symm y, ?_⟩
    apply (scalarProjectiveGeneralLinearEquiv n K).injective
    rw [scalarPSLInclusion_native, MulEquiv.apply_symm_apply]
    exact hy

instance scalarPSLRangeNormal (n : ℕ) (K : Type u) [Field K] : (scalarPSLRange n K).Normal := by
  rw [scalarPSLRange_eq_comap]
  infer_instance


abbrev scalarFixedPGL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :=
  TauCeti.fixedSubgroup (scalarPGLGraphFieldAut n K sigma).toMonoidHom

abbrev scalarFixedT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (scalarFixedPGL n K sigma) :=
  (scalarPSLRange n K).subgroupOf (scalarFixedPGL n K sigma)

instance scalarFixedTNormal (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    (scalarFixedT n K sigma).Normal := by
  change ((scalarPSLRange n K).comap (scalarFixedPGL n K sigma).subtype).Normal
  infer_instance


end

end CFSG.ComponentClassification.CatalogueBGraphField
