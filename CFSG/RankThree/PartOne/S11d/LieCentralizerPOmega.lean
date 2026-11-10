module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def statedOmegaOrthEquiv (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃* orthDerived Q :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

theorem coe_statedOmegaOrthEquiv (hQ : ⇑Q = Q₀) (A : StatedOmega Q₀) :
    (statedOmegaOrthEquiv hQ A : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A :=
  rfl

@[expose] noncomputable def statedProjOrthEquiv (hQ : ⇑Q = Q₀) :
    StatedProj (StatedOmega Q₀) ≃* ProjOrthDerived Q :=
  QuotientGroup.congr _ _ (statedOmegaOrthEquiv hQ) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
      rw [Subgroup.mem_subgroupOf]
      change ((statedOmegaOrthEquiv hQ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈
        scalars K (ι → K)
      rw [coe_statedOmegaOrthEquiv]
      exact hy
    · intro hx
      refine ⟨(statedOmegaOrthEquiv hQ).symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : (statedOmegaOrthEquiv hQ ((statedOmegaOrthEquiv hQ).symm x) :
          (ι → K) ≃ₗ[K] (ι → K)) = x := by rw [MulEquiv.apply_symm_apply]
      rw [coe_statedOmegaOrthEquiv] at h1
      rw [h1]
      exact hx)

end Bridge


end CFSG.RankThree.PartOne
