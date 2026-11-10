module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullPartition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

universe u v

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

theorem central_involution_translate_isInvolution
    (u x : G) (hu : IsInvolution u) (hx : IsInvolution x)
    (huZ : u ∈ Subgroup.center G) (hxu : x ≠ u) : IsInvolution (u * x) := by
  have hcomm : Commute u x := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp huZ x).symm
  refine ⟨?_, by rw [hcomm.mul_pow 2, hu.sq_eq_one, hx.sq_eq_one, one_mul]⟩
  intro hmul
  apply hxu
  have heq := congrArg (fun y : G => u * y) hmul
  simpa only [← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul, mul_one] using heq


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
