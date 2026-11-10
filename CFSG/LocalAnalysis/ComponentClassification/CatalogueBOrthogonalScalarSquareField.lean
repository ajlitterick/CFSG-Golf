module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldFrobenius

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]


theorem scalar_square_actual_finite_dimension [Nontrivial V] [Module.Finite K V]
    (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    Module.Finite (scalarAlgebra T) V ∧
      Module.finrank K V = 2 * Module.finrank (scalarAlgebra T) V ∧
      Module.finrank (scalarAlgebra T) V = Module.finrank K V / 2 := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  exact ⟨evaluationModule_finite T, evaluationModule_finrank T d hns hsquare,
    evaluationModule_finrank_div_two T d hns hsquare⟩


end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
