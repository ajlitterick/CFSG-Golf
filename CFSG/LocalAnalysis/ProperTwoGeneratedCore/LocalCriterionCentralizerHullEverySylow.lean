module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem normal_root_mem_every_point_sylow
    (H U : Subgroup G) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal] (T : Sylow 2 H) :
    U ≤ (T : Subgroup H).map H.subtype := by
  let : IsElementaryAbelian 2 (U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  have hle : U.subgroupOf H ≤ (T : Subgroup H) :=
    (IsElementaryAbelian.isPGroup 2 (U.subgroupOf H)).le_sylow_of_normal T
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  simpa only [Subgroup.map_subgroupOf_eq_of_le hUH] using hmap


theorem entire_root_nonidentity_set
    (L H U : Subgroup G)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x}) :
    (U : Set G) \ {1} = {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x} := by
  ext x
  change (x ∈ (U : Set G) ∧ x ≠ 1) ↔ _
  rw [hU]
  constructor
  · rintro ⟨hx | hx, hxone⟩
    · exact (hxone hx).elim
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, hx.2.2.ne_one⟩


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
