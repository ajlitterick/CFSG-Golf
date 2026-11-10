module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def orthElementaryMap (Q : QuadraticForm K V) (u v : V) : V →ₗ[K] V :=
  eichlerLin Q u v

theorem orthElementaryMap_apply (Q : QuadraticForm K V) (u v x : V) :
    orthElementaryMap Q u v x =
      x + polar Q x u • v - polar Q x v • u - (Q v * polar Q x u) • u := by
  rw [orthElementaryMap, eichlerLin_apply, add_smul]
  abel

theorem orthogonal_elementary_addition (Q : QuadraticForm K V) {u v w : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) (hw : polar Q u w = 0) :
    orthElementaryMap Q u 0 = LinearMap.id ∧
      (orthElementaryMap Q u v).comp (orthElementaryMap Q u w) = orthElementaryMap Q u (v + w) ∧
      (orthElementaryMap Q u v).comp (orthElementaryMap Q u (-v)) = LinearMap.id ∧
      (orthElementaryMap Q u (-v)).comp (orthElementaryMap Q u v) = LinearMap.id := by
  have hv' : polar Q u (-v) = 0 := by rw [polar_neg_right, hv, neg_zero]
  have hzero : orthElementaryMap Q u 0 = LinearMap.id :=
    LinearMap.ext fun x => eichlerLin_zero_right Q u x
  refine ⟨hzero, LinearMap.ext fun x => eichlerLin_comp hu hv hw x, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, orthElementaryMap, orthElementaryMap, eichlerLin_comp hu hv hv',
      add_neg_cancel, eichlerLin_zero_right, LinearMap.id_apply]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, orthElementaryMap, orthElementaryMap, eichlerLin_comp hu hv' hv,
      neg_add_cancel, eichlerLin_zero_right, LinearMap.id_apply]


@[expose] def orthElementaryGroup (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  elementaryGroup Q


theorem mem_orthElementaryGroup_gen (Q : QuadraticForm K V) {u v : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) :
    ∃ g ∈ orthElementaryGroup Q, (g : V →ₗ[K] V) = orthElementaryMap Q u v :=
  ⟨eichler Q u v, eichler_mem_elementaryGroup Q u v, LinearMap.ext fun x => eichler_apply hu hv x⟩


theorem orthElementaryGroup_le (Q : QuadraticForm K V) :
    orthElementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q


theorem orthogonal_elementary_normality (Q : QuadraticForm K V) :
    orthElementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ((orthElementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal :=
  ⟨elementaryGroup_le_orthogonalGroup Q, elementaryGroup_subgroupOf_normal Q⟩


end CFSG.LocalAnalysis.ComponentInitial
