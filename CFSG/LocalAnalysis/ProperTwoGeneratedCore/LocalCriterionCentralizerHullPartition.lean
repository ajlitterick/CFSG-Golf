module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullInnerLift

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

universe u

variable {G : Type u} [Group G]


theorem hull_involution_three_sets_disjoint (L : Subgroup G) (u : G) (huL : u ∉ L) :
    Disjoint ({u} : Set G) {x : G | x ∈ L ∧ IsInvolution x} ∧
      Disjoint ({u} : Set G)
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint {x : G | x ∈ L ∧ IsInvolution x}
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro x hx hxL
    exact huL (Set.mem_singleton_iff.mp hx ▸ hxL.1)
  · intro x hx htranslate
    have hxu := Set.mem_singleton_iff.mp hx
    subst x
    obtain ⟨l, hl, hmul⟩ := htranslate
    apply hl.2.ne_one
    have heq : u * l = u * 1 := by simpa only [mul_one] using hmul
    exact mul_left_cancel heq
  · intro x hx
    rintro ⟨l, hl, rfl⟩
    have humem := L.mul_mem hx.1 (L.inv_mem hl.1)
    apply huL
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using humem


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
