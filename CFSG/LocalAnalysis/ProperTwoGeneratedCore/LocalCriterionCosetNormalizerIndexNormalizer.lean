module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCapture

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem cosetUnitSet_subset_point (H : Subgroup G) (z u : G) :
    cosetUnitSet H z u ⊆ (H : Set G) := by
  intro v hv
  rcases hv with hv | hv
  · exact Set.mem_singleton_iff.mp hv ▸ H.one_mem
  · exact hv.2

theorem translatedCosetUnitSet_subset_point (H : Subgroup G) (z u : G)
    (huH : u ∈ H) : translatedCosetUnitSet H z u ⊆ (H : Set G) := by
  rintro s ⟨v, hv, rfl⟩
  exact H.mul_mem huH (cosetUnitSet_subset_point H z u hv)

theorem translated_coset_normalizer_le_point [Finite G]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (huH : u ∈ H) (hzu : Commute z u) :
    Subgroup.normalizer (translatedCosetUnitSet H z u) ≤ H := by
  have huDelta : u ∈ translatedCosetUnitSet H z u :=
    ⟨1, Set.mem_union_left _ (Set.mem_singleton 1), mul_one u⟩
  have hzU : z ∈ cosetUnitSet H z u := by
    right
    exact ⟨⟨distinguished_mem_pointClass z, Subgroup.mem_centralizer_singleton_iff.mpr hzu⟩,
      h.distinguished_mem⟩
  have huzDelta : u * z ∈ translatedCosetUnitSet H z u := ⟨z, hzU, rfl⟩
  have hclassfix :=
    ((involution_point_unique_containment_action h.distinguished_mem h.distinguished_order).2
      h.unique_containment).2.1
  intro x hx
  have hxu : x * u * x⁻¹ ∈ H := translatedCosetUnitSet_subset_point H z u huH
    ((show ∀ s, s ∈ translatedCosetUnitSet H z u ↔
      x * s * x⁻¹ ∈ translatedCosetUnitSet H z u from hx) u |>.mp huDelta)
  have hxuz : x * (u * z) * x⁻¹ ∈ H := translatedCosetUnitSet_subset_point H z u huH
    ((show ∀ s, s ∈ translatedCosetUnitSet H z u ↔
      x * s * x⁻¹ ∈ translatedCosetUnitSet H z u from hx) (u * z) |>.mp huzDelta)
  have hxz : x * z * x⁻¹ ∈ H := by
    have hh := H.mul_mem (H.inv_mem hxu) hxuz
    have hm := map_mul (MulAut.conj x).toMonoidHom u z
    change x * (u * z) * x⁻¹ = (x * u * x⁻¹) * (x * z * x⁻¹) at hm
    rw [hm, inv_mul_cancel_left] at hh
    exact hh
  have hsclass : rightConjugateElem z x⁻¹ ∈ involutionPointClass z :=
    pointClass_right_conjugate_mem (distinguished_mem_pointClass z) x⁻¹
  have hsH : rightConjugateElem z x⁻¹ ∈ H := by
    simpa only [rightConjugateElem, inv_inv] using hxz
  have hsbase := (point_right_base_fixed_iff H _).mpr hsH
  have hsother := point_right_fixed_conjugate
    ((point_right_base_fixed_iff H z).mpr h.distinguished_mem) x⁻¹
  obtain ⟨omega, _, huniq⟩ := hclassfix _ hsclass
  have hxfixed : pointRightCosetMul H (rightCosetMk H 1) x⁻¹ = rightCosetMk H 1 :=
    (huniq _ hsother).trans (huniq _ hsbase).symm
  exact H.inv_mem_iff.mp ((point_right_base_fixed_iff H x⁻¹).mp hxfixed)


theorem translated_normalizer_centralizer_eq_point_centralizer [Finite G]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (huH : u ∈ H) (hzu : Commute z u) :
    Subgroup.normalizer (translatedCosetUnitSet H z u) ⊓
      Subgroup.centralizer ({u} : Set G) =
    Subgroup.centralizer ({u} : Set G) ⊓ H := by
  apply le_antisymm
  · exact fun _ hx => ⟨hx.2, translated_coset_normalizer_le_point h huH hzu hx.1⟩
  · exact fun _ hx => ⟨point_centralizer_le_translated_normalizer H z u hx, hx.1⟩


end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
