module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarKernelReduction
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasTwo

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {σ : K ≃+* K}

theorem fixesSingularLines_of_scalar (T : V ≃ₛₗ[σ.toRingHom] V) (a : Kˣ)
    (ha : ∀ v, T v = (a : K) • v) : FixesSingularLines Q T := by
  apply (fixesSingularLines_iff_vectors T).mpr
  exact fun v _ _ => ⟨a, ha v⟩

theorem scalar_kernel_actions [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hS : ∃ S : Submodule K V, finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) (hfix : FixesSingularLines Q T) :
    σ = RingEquiv.refl K ∧ ∃ a : Kˣ, (∀ v, T v = (a : K) • v) ∧
      (∀ v, T.symm v = (↑(a⁻¹) : K) • v) ∧ (μ : K) = (a : K) ^ 2 := by
  obtain ⟨S, hS3, hSs⟩ := hS
  obtain ⟨e, heS, he0⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_ne_zero_of_one_le_finrank (T := S) (by omega)
  obtain ⟨P, R, _, _, hPR, _, _⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quadratic_three_hyperbolic_pairs hQ
      ⟨S, hS3, hSs⟩ (hSs e heS) he0
  exact scalar_of_two_pairs hPR T μ hT ((fixesSingularLines_iff_vectors T).mp hfix)


end CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel
