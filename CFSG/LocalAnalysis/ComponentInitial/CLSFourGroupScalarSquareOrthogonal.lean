module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonalModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary Module QuadraticMap
open CFSG.ComponentClassification CatalogueBOrthogonalScalarSquare
  CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquareStructure

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signEquiv_empty (c : Basis ι K V) : signEquiv c ∅ = 1 := by
  have h := signEquiv_mul_self c ∅
  rwa [signEquiv_mul, symmDiff_self, Finset.bot_eq_empty] at h


end Sign

theorem apply_of_mem_positiveSquareKernel {A : V ≃ₗ[K] V} {b : K} (hb : b ≠ 0) {v : V}
    (hv : v ∈ positiveSquareKernel A b) : A v = b • v := by
  have h := LinearMap.mem_ker.1 hv
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, sub_eq_zero] at h
  calc A v = b • (b⁻¹ • A v) := by rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
    _ = b • v := by rw [h]

theorem apply_of_mem_negativeSquareKernel {A : V ≃ₗ[K] V} {b : K} (hb : b ≠ 0) {v : V}
    (hv : v ∈ negativeSquareKernel A b) : A v = (-b) • v := by
  have h := LinearMap.mem_ker.1 hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, add_eq_zero_iff_eq_neg] at h
  calc A v = b • (b⁻¹ • A v) := by rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
    _ = (-b) • v := by rw [h, smul_neg, neg_smul]

section Systems

variable {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}


end Systems

section Field

variable {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}

theorem two_ne_zero_of_algebra (hK : ringChar K ≠ 2) {E : Type*} [Field E] [Algebra K E] :
    (2 : E) ≠ 0 := by
  rw [← map_ofNat (algebraMap K E) 2]
  exact (map_ne_zero (algebraMap K E)).2 (Ring.two_ne_zero hK)


theorem exists_orthonormal_of_eq_pow {E : Type*} [Field E] {W : Type*} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {ℓ f : ℕ} (hUF : UnitaryFieldData ℓ f E)
    {τ : E →+* E} (hτ : ∀ z, τ z = z ^ (ℓ ^ f)) (h : W →ₛₗ[τ] W →ₗ[E] E) (hs : h.IsSymm)
    (hl : h.SeparatingLeft) :
    ∃ ob : Basis (Fin (finrank E W)) E W, ∀ i j, h (ob i) (ob j) = if i = j then 1 else 0 := by
  have hb : τ = hUF.bar := RingHom.ext fun z => by rw [hτ, hUF.bar_apply]
  subst hb
  exact hUF.exists_orthonormal_basis hs hl


end Field


end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
