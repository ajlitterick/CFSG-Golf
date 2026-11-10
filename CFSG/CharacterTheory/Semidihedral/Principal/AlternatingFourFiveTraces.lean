module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicMultiplicity
public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.TraceGap
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.CosetConstantKernel

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u w

namespace AlternatingFourFive


theorem trace_idempotent_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (P : Module.End ℂ V) (hP : IsIdempotentElem P) :
    ∃ m : ℕ, LinearMap.trace ℂ V P = m :=
  ⟨Module.finrank ℂ (LinearMap.range P), (LinearMap.IsIdempotentElem.isProj_range P hP).trace⟩


theorem trace_mul_finiteOrderEigenprojection {G : Type*} [Group G]
    (θ : FiniteComplexRepresentation G) (y w₀ : G) (n : ℕ) (hn : 0 < n) (μ : ℂˣ) :
    LinearMap.trace ℂ θ.vector (θ.representation y * finiteOrderEigenprojection n
      (Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn.ne')) μ (θ.representation w₀)) =
      (n : ℂ)⁻¹ * ∑ j ∈ Finset.range n, ((μ⁻¹ : ℂˣ) : ℂ) ^ j * θ.character (y * w₀ ^ j) := by
  rw [finiteOrderEigenprojection, cyclicOperatorAverage, mul_smul_comm, Finset.mul_sum,
    map_smul, map_sum, smul_eq_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_pow, mul_smul_comm, map_smul, smul_eq_mul]
  congr 1
  change LinearMap.trace ℂ θ.vector (θ.representation y * θ.representation w₀ ^ j) =
    LinearMap.trace ℂ θ.vector (θ.representation (y * w₀ ^ j))
  rw [map_mul θ.representation, map_pow θ.representation]


end AlternatingFourFive

open AlternatingFourFive


end CFSG.Semidihedral.Principal
