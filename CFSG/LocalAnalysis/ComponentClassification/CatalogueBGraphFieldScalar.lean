module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphForm

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField
open CatalogueBHigherLinearInner

universe u

abbrev glScalarCenter (n : ℕ) (K : Type u) [Field K] : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range

theorem glScalarCenter_eq_center (n : ℕ) (K : Type u) [Field K] :
    glScalarCenter n K = Subgroup.center (GL (Fin n) K) :=
  GeneralLinearGroup.center_eq_range_scalar.symm

instance glScalarCenterNormal (n : ℕ) (K : Type u) [Field K] : (glScalarCenter n K).Normal := by
  rw [glScalarCenter_eq_center]
  infer_instance

abbrev ScalarProjectiveGeneralLinear (n : ℕ) (K : Type u) [Field K] :=
  GL (Fin n) K ⧸ glScalarCenter n K

@[expose] def scalarProjectiveGeneralLinearEquiv (n : ℕ) (K : Type u) [Field K] :
    ScalarProjectiveGeneralLinear n K ≃* ProjGenLinGroup (Fin n) K :=
  QuotientGroup.quotientMulEquivOfEq (glScalarCenter_eq_center n K)


@[expose] def scalarPGLGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (ScalarProjectiveGeneralLinear n K) :=
  MulAut.congr (scalarProjectiveGeneralLinearEquiv n K).symm (pglGraphFieldAut n K sigma)


end

end CFSG.ComponentClassification.CatalogueBGraphField
