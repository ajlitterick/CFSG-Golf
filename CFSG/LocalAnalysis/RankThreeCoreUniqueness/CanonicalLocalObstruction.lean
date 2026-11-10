module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedCentralizerObstruction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem finite_perfectResidual_eq_bot_iff_solvable
    {G : Type*} [Group G] [Finite G] :
    perfectResidual G = ⊥ ↔ Group.IsSolvable G := by
  constructor
  · intro hbottom
    obtain ⟨index, hindex⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
    exact ⟨index, hindex.symm.trans hbottom⟩
  · rintro ⟨index, hindex⟩
    exact le_bot_iff.mp ((iInf_le _ index).trans hindex.le)

theorem finite_perfectResidual_map_eq
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    Subgroup.map homomorphism (perfectResidual G) = perfectResidual Image := by
  apply le_antisymm
  · apply le_iInf
    intro index
    exact (Subgroup.map_mono (iInf_le _ index)).trans
      (map_derivedSeries_le_derivedSeries homomorphism index)
  · obtain ⟨index, hindex⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
    have hbound := derivedSeries_le_map_derivedSeries hsurjective index
    rw [← hindex] at hbound
    exact (iInf_le _ index).trans hbound

theorem perfect_subgroup_le_perfectResidual
    {G : Type*} [Group G] (perfectGroup : Subgroup G)
    (hperfect : Group.IsPerfect perfectGroup) : perfectGroup ≤ perfectResidual G := by
  apply le_iInf
  intro index
  induction index with
  | zero => exact le_top
  | succ index hinduction =>
    rw [derivedSeries_succ, ← Subgroup.isPerfect_iff.mp hperfect]
    exact Subgroup.commutator_mono hinduction hinduction

theorem perfect_subgroup_le_perfectResidualOf
    {G : Type*} [Group G] (perfectGroup overgroup : Subgroup G)
    (hperfect : Group.IsPerfect perfectGroup) (hcontained : perfectGroup ≤ overgroup) :
    perfectGroup ≤ perfectResidualOf overgroup := by
  have hinternal : Group.IsPerfect (perfectGroup.subgroupOf overgroup) := by
    apply Subgroup.isPerfect_iff.mpr
    have hmap := Subgroup.map_commutator (perfectGroup.subgroupOf overgroup)
      (perfectGroup.subgroupOf overgroup) overgroup.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hcontained, Subgroup.isPerfect_iff.mp hperfect] at hmap
    apply (Subgroup.map_injective overgroup.subtype_injective)
    exact hmap.trans (Subgroup.map_subgroupOf_eq_of_le hcontained).symm
  have hbound := Subgroup.map_mono (f := overgroup.subtype)
    (perfect_subgroup_le_perfectResidual (perfectGroup.subgroupOf overgroup) hinternal)
  rwa [Subgroup.map_subgroupOf_eq_of_le hcontained] at hbound


end CFSG.RankThreeCoreUniqueness.Helpers
