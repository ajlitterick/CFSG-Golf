module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityAlgebra

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem original_class_unique_fixed_on_invariant_set
    [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (A : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta, pointRightCosetMul H omega a ∈ Delta)
    (x : A) (hx : x.val ∈ involutionPointClass z)
    (hwitness : ∃ omega ∈ Delta, pointRightCosetMul H omega x.val = omega) :
    letI := pointInvariantSetInverseRightAction H A Delta hstable
    ∃! omega : Delta, x • omega = omega := by
  let := pointInvariantSetInverseRightAction H A Delta hstable
  obtain ⟨a, ha, hax⟩ := hwitness
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨_b, _hb, hxb⟩ := huniq x.val hx
  have hfixInverse : pointRightCosetMul H a x.val⁻¹ = a := by
    have hh := congrArg (fun omega => pointRightCosetMul H omega x.val⁻¹) hax
    simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one] using hh.symm
  refine ⟨⟨a, ha⟩, Subtype.ext hfixInverse, ?_⟩
  intro omega hfix
  apply Subtype.ext
  have hfixRight : pointRightCosetMul H omega.val x.val = omega.val := by
    have hh := congrArg (fun b : Delta => pointRightCosetMul H b.val x.val) hfix
    change pointRightCosetMul H (pointRightCosetMul H omega.val x.val⁻¹) x.val =
      pointRightCosetMul H omega.val x.val at hh
    simpa only [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one] using hh.symm
  exact (hxb omega.val hfixRight).trans (hxb a hax).symm


end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
