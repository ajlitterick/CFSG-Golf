module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointKernelBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointKernel

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def detwist (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  { (coordinateFieldMap d sigma.symm).trans T.toAddEquiv with
    map_smul' a v := by
      change T (coordinateFieldMap d sigma.symm (a • v)) =
        a • T (coordinateFieldMap d sigma.symm v)
      rw [coordinateFieldMap_smul, T.map_smulₛₗ]
      change sigma (sigma.symm a) • T (coordinateFieldMap d sigma.symm v) = _
      rw [sigma.apply_symm_apply] }

theorem detwist_apply (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    detwist sigma T v = T (fun i => sigma.symm (v i)) := rfl


theorem detwist_twist (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    detwist sigma T (coordinateFieldMap d sigma v) = T v := by
  rw [detwist_apply]
  congr 1
  funext i
  exact sigma.symm_apply_apply (v i)


@[expose] def realizingMatrix (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) : GL (Fin d) K :=
  matrixLinearIso.symm (detwist sigma T)

theorem realizingMatrix_linearEquiv (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    matrixLinearEquiv (realizingMatrix sigma T) = detwist sigma T :=
  matrixLinearIso.apply_symm_apply (detwist sigma T)


@[expose] def realizingPair (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearGroup d K := SemidirectProduct.mk (realizingMatrix sigma T) sigma


theorem realizingPair_right (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    (realizingPair sigma T).right = sigma := rfl

theorem realizingPair_apply (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    coordinateSemilinearMap (realizingPair sigma T) v = T v := by
  change matrixLinearEquiv (realizingMatrix sigma T) (coordinateFieldMap d sigma v) = _
  rw [realizingMatrix_linearEquiv, detwist_twist]

theorem realizingPair_addEquiv (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearMap (realizingPair sigma T) = T.toAddEquiv :=
  AddEquiv.ext (realizingPair_apply sigma T)


theorem realizingPair_linearMap (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearLinearMap (realizingPair sigma T) = T.toLinearMap :=
  LinearMap.ext (realizingPair_apply sigma T)


end CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization
