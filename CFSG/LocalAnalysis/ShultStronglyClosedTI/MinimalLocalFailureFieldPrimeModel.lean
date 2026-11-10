module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeHullCount
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeModelParameter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFlip
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeLocal

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open scoped MatrixGroups commutatorElement
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

theorem baseOrbit_eq_hull {H Y : Subgroup G} {r : G} (hrY : r ∈ Y)
    (hlocalY : InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hrY⟩ : Y)) :
    baseOrbit H Y = baseOrbit H (Subgroup.closure (conjugacyWithin Y r)) := by
  have hLY : Subgroup.closure (conjugacyWithin Y r) ≤ Y := by
    apply (Subgroup.closure_le _).mpr
    rintro w ⟨k, rfl⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem k.2) hrY) k.2
  obtain ⟨-, htrans, -⟩ := involution_point_hull_controls_class hlocalY
  have hmap := CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.internal_hull_map Y hrY
  ext omega
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨l, hl⟩ := htrans (rightCosetMk (H.subgroupOf Y) 1)
      (rightCosetMk (H.subgroupOf Y) ⟨g, hg⟩)
    refine ⟨((l : Y) : G), ?_, ?_⟩
    · have hmem := Subgroup.mem_map_of_mem Y.subtype l.2
      rw [hmap] at hmem
      exact hmem
    · have himage := congrArg (restrictedRightCosetEmbedding H Y) hl
      rw [restrictedRightCosetEmbedding_translate, restrictedRightCosetEmbedding_base] at himage
      rw [himage]
      exact (translate_base_mk H g).symm
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hLY hg, rfl⟩

omit [Finite G] in
theorem involutionCore_closure_eq_top {S : Set G} (hS : ∀ s ∈ S, IsInvolution s) :
    involutionCore (Subgroup.closure S) = ⊤ := by
  apply top_unique
  rw [← Subgroup.closure_closure_coe_preimage (k := S)]
  apply Subgroup.closure_mono
  intro x hx
  have hxS := hS _ hx
  exact ⟨fun h1 => hxS.1 (congrArg Subtype.val h1), Subtype.ext (by simpa using hxS.2)⟩


end CFSG.ShultStronglyClosedTI.CyclicSemiregular
