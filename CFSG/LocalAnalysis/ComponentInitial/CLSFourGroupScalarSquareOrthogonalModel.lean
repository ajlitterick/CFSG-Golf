module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareModel
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Proj

variable (Q : QuadraticForm K V)

abbrev orthogonalOmega : Subgroup (V ≃ₗ[K] V) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

@[expose] def omegaScalars : Subgroup (orthogonalOmega Q) where
  carrier := {g | ∃ c : K, ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id}
  one_mem' := ⟨1, by ext; simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c * c', LinearMap.ext fun v => ?_⟩
    have h1 := LinearMap.congr_fun hc (((b : V ≃ₗ[K] V) : V →ₗ[K] V) v)
    have h2 := LinearMap.congr_fun hc' v
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
    change (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = (c * c') • v
    rw [h1, h2, smul_smul]
  inv_mem' := by
    rintro a ⟨c, hc⟩
    refine ⟨c⁻¹, LinearMap.ext fun v => ?_⟩
    have hav : ∀ w, (a : V ≃ₗ[K] V) w = c • w := fun w => LinearMap.congr_fun hc w
    have hinv : ∀ w, (a : V ≃ₗ[K] V) (((a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) w) = w :=
      fun w => by
        change ((a * a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) w = w
        rw [mul_inv_cancel]
        rfl
    change ((a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v = c⁻¹ • v
    by_cases hc0 : c = 0
    · have hz : ∀ w : V, w = 0 := fun w => by rw [← hinv w, hav, hc0, zero_smul]
      rw [hz (((a⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v), hz v, smul_zero]
    · apply (a : V ≃ₗ[K] V).injective
      rw [hinv, hav, smul_smul, mul_inv_cancel₀ hc0, one_smul]

theorem mem_omegaScalars {g : orthogonalOmega Q} :
    g ∈ omegaScalars Q ↔ ∃ c : K, ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id :=
  Iff.rfl

instance omegaScalars_normal : (omegaScalars Q).Normal :=
  ⟨fun n ⟨c, hc⟩ g => ⟨c, LinearMap.ext fun v => by
    have h1 := LinearMap.congr_fun hc (((g⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v)
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at h1
    change (g : V ≃ₗ[K] V) ((n : V ≃ₗ[K] V) (((g⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v)) = c • v
    rw [h1, map_smul]
    change c • ((g * g⁻¹ : orthogonalOmega Q) : V ≃ₗ[K] V) v = c • v
    rw [mul_inv_cancel]
    rfl⟩⟩

abbrev OrthogonalProj : Type _ :=
  orthogonalOmega Q ⧸ omegaScalars Q

@[expose] def orthogonalProj : orthogonalOmega Q →* OrthogonalProj Q :=
  QuotientGroup.mk' (omegaScalars Q)

end Proj

section Pairs

variable {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}

@[expose] def NotScalar (g : V ≃ₗ[K] V) : Prop :=
  ∀ c : K, (g : V →ₗ[K] V) ≠ c • LinearMap.id


end Pairs

section Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def signEquiv (c : Basis ι K V) (S : Finset ι) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin c c (signDiag S)) (Matrix.toLin c c (signDiag S))
    (by rw [← Matrix.toLin_mul, signDiag_mul_self, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, signDiag_mul_self, Matrix.toLin_one])

theorem coe_signEquiv (c : Basis ι K V) (S : Finset ι) :
    ((signEquiv c S : V ≃ₗ[K] V) : V →ₗ[K] V) = Matrix.toLin c c (signDiag S) :=
  rfl

theorem signEquiv_mul (c : Basis ι K V) (S T : Finset ι) :
    signEquiv c S * signEquiv c T = signEquiv c (symmDiff S T) := by
  refine LinearEquiv.toLinearMap_injective ?_
  change Matrix.toLin c c (signDiag S) ∘ₗ Matrix.toLin c c (signDiag T) =
    Matrix.toLin c c (signDiag (symmDiff S T))
  rw [← Matrix.toLin_mul, signDiag_mul_signDiag]

theorem signEquiv_mul_self (c : Basis ι K V) (S : Finset ι) :
    signEquiv c S * signEquiv c S = 1 := by
  rw [signEquiv_mul, symmDiff_self]
  refine LinearEquiv.toLinearMap_injective ?_
  change Matrix.toLin c c (signDiag ⊥) = LinearMap.id
  rw [show (⊥ : Finset ι) = ∅ from rfl]
  rw [show signDiag (K := K) (∅ : Finset ι) = 1 by
    rw [signDiag]
    simp [diagonal_one], Matrix.toLin_one]

theorem signEquiv_comm (c : Basis ι K V) (S T : Finset ι) :
    signEquiv c S * signEquiv c T = signEquiv c T * signEquiv c S := by
  rw [signEquiv_mul, signEquiv_mul, symmDiff_comm]

theorem det_signEquiv (c : Basis ι K V) (S : Finset ι) :
    (LinearEquiv.det (signEquiv c S) : K) = (-1) ^ S.card := by
  rw [LinearEquiv.coe_det, coe_signEquiv, LinearMap.det_toLin, det_signDiag]


theorem signEquiv_preserves (B : LinearMap.BilinForm K V) (c : Basis ι K V) {S : Finset ι}
    (hS : ∀ i j, B (c i) (c j) ≠ 0 → (i ∈ S ↔ j ∈ S)) (v w : V) :
    B (signEquiv c S v) (signEquiv c S w) = B v w :=
  toLin_preserves B c (Matrix.of fun i j => B (c i) (c j)) (fun _ _ => rfl) (fun _ _ => rfl)
    (signDiag_conj fun i j h => hS i j h) v w


end Sign

end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
