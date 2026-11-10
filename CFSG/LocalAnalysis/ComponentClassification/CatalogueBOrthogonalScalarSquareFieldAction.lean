module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[expose, instance_reducible] def evaluationModule (T : Module.End K V) :
    Module (scalarAlgebra T) V :=
  Subalgebra.moduleLeft (scalarAlgebra T)

theorem evaluation_smul (T : Module.End K V) (z : scalarAlgebra T) (v : V) :
    letI := evaluationModule T
    z • v = z.val v := rfl

theorem evaluation_generator_smul (T : Module.End K V) (v : V) :
    letI := evaluationModule T
    generator T • v = T v := rfl

theorem evaluation_algebraMap_smul (T : Module.End K V) (a : K) (v : V) :
    letI := evaluationModule T
    algebraMap K (scalarAlgebra T) a • v = a • v := rfl

theorem evaluationScalarTower (T : Module.End K V) :
    letI := evaluationModule T
    IsScalarTower K (scalarAlgebra T) V := by
  let := evaluationModule T
  exact IsScalarTower.of_algebraMap_smul (evaluation_algebraMap_smul T)

theorem evaluationCompatibleSMul (T : Module.End K V) :
    letI := evaluationModule T
    LinearMap.CompatibleSMul V V K (scalarAlgebra T) := by
  let := evaluationModule T
  refine ⟨fun L a v => ?_⟩
  simpa only [evaluation_algebraMap_smul] using
    L.map_smul (algebraMap K (scalarAlgebra T) a) v

theorem evaluationModule_finite [Module.Finite K V] (T : Module.End K V) :
    letI := evaluationModule T
    Module.Finite (scalarAlgebra T) V := by
  let := evaluationModule T
  let := evaluationScalarTower T
  exact Module.Finite.of_restrictScalars_finite K (scalarAlgebra T) V

theorem evaluationModule_finrank [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    Module.finrank K V = 2 * Module.finrank (scalarAlgebra T) V := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := evaluationScalarTower T
  simpa only [scalarAlgebra_finrank T d hns hsquare] using
    (Module.finrank_mul_finrank K (scalarAlgebra T) V).symm

theorem evaluationModule_finrank_div_two [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    Module.finrank (scalarAlgebra T) V = Module.finrank K V / 2 := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  rw [evaluationModule_finrank T d hns hsquare]
  omega

theorem commute_evaluation (T L : Module.End K V) (hLT : Commute L T)
    (z : scalarAlgebra T) : Commute L z.val :=
  Algebra.commute_of_mem_adjoin_singleton_of_commute z.property hLT

theorem commute_iff_evaluation_linear (T L : Module.End K V) :
    letI := evaluationModule T
    Commute L T ↔ ∀ (z : scalarAlgebra T) (v : V), L (z • v) = z • L v := by
  let := evaluationModule T
  constructor
  · intro hLT z v
    exact congrArg (fun F : Module.End K V => F v) (commute_evaluation T L hLT z).eq
  · intro hL
    apply LinearMap.ext
    intro v
    exact hL (generator T) v


end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
