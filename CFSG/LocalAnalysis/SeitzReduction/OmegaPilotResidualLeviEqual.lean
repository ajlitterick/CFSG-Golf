module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviAssembly

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Similarity

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem polar_coordinateSemilinearMap (g : similarityPairs Q) (a b : Fin d → K) :
    QuadraticMap.polar Q (coordinateSemilinearMap g.val a) (coordinateSemilinearMap g.val b) =
      (multiplier Q g : K) * g.val.right (QuadraticMap.polar Q a b) := by
  simp only [QuadraticMap.polar, ← map_add, multiplier_spec, map_sub, mul_sub]

theorem mem_ker_iff_polar (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (v : Fin d → K) : v ∈ LinearMap.ker N ↔ ∀ x, QuadraticMap.polar Q (N x) v = 0 := by
  constructor
  · intro hv x
    rw [← QuadraticMap.polarBilin_apply_apply, hadj, LinearMap.mem_ker.mp hv, map_zero]
  · intro h
    rw [LinearMap.mem_ker]
    refine hB.2 _ fun x => ?_
    rw [← hadj, QuadraticMap.polarBilin_apply_apply]
    exact h x

theorem symm_mem_ker_of_mapsTo_range (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (g : similarityPairs Q)
    (hTr : ∀ u ∈ LinearMap.range N, coordinateSemilinearMap g.val u ∈ LinearMap.range N) :
    ∀ v ∈ LinearMap.ker N, (coordinateSemilinearMap g.val).symm v ∈ LinearMap.ker N := by
  intro v hv
  rw [mem_ker_iff_polar hB N hadj] at hv ⊢
  intro x
  obtain ⟨y, hy⟩ := hTr (N x) (LinearMap.mem_range_self N x)
  have h1 := polar_coordinateSemilinearMap g (N x) ((coordinateSemilinearMap g.val).symm v)
  rw [AddEquiv.apply_symm_apply, ← hy, hv y] at h1
  have h2 := (mul_eq_zero.mp h1.symm).resolve_left (Units.ne_zero _)
  exact (map_eq_zero_iff g.val.right g.val.right.injective).mp h2

end Similarity

section Kernel


end Kernel

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)


end Plus

section FixedSpace


end FixedSpace

end CFSG.SeitzReduction.OmegaPilot
