module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealizationBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointAction CatalogueBOrthogonalPointKernel

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def realizingSimilarity (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) : similarityPairs Q :=
  ⟨realizingPair sigma T, ⟨mu, by
    intro v
    change Q (coordinateSemilinearMap (realizingPair sigma T) v) =
      (mu : K) * sigma (Q v)
    rw [realizingPair_apply]
    exact hT v⟩⟩


theorem realizingSimilarity_linearMap (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    coordinateSemilinearLinearMap (realizingSimilarity Q sigma T mu hT).val = T.toLinearMap :=
  realizingPair_linearMap sigma T


theorem realizingSimilarity_point_submodule (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (L : Points Q) :
    (similarityPointAction Q (realizingSimilarity Q sigma T mu hT) L).val =
      L.val.map T.toLinearMap := by
  rw [similarityPointAction_submodule, realizingSimilarity_linearMap]
  rfl


theorem pointPerm_eq_realizingSimilarity (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (phi : Equiv.Perm (Points Q))
    (hphi : ∀ L : Points Q, (phi L).val = L.val.map T.toLinearMap) :
    phi = similarityPointAction Q (realizingSimilarity Q sigma T mu hT) := by
  apply Equiv.ext
  intro L
  apply Subtype.ext
  exact (hphi L).trans (realizingSimilarity_point_submodule Q sigma T mu hT L).symm

theorem pointPerm_mem_similarityPointImage (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (phi : Equiv.Perm (Points Q))
    (hphi : ∀ L : Points Q, (phi L).val = L.val.map T.toLinearMap) :
    phi ∈ similarityPointImage Q :=
  ⟨realizingSimilarity Q sigma T mu hT,
    (pointPerm_eq_realizingSimilarity Q sigma T mu hT phi hphi).symm⟩


end CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization
