module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]


theorem point_right_coset_kernel_iff (H : Subgroup G) (g : G) :
    (∀ omega : pointRightCosetSpace H, pointRightCosetMul H omega g = omega) ↔
      g ∈ H.normalCore := by
  rw [H.normalCore_eq_iInf_comap_conj]
  constructor
  · intro hfix
    apply Subgroup.mem_iInf.mpr
    intro x
    have hx := hfix (Quotient.mk (QuotientGroup.rightRel H) x)
    rw [pointRightCosetMul_mk] at hx
    have hrel := Quotient.exact hx.symm
    change QuotientGroup.rightRel H x (x * g) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    change x * g * x⁻¹ ∈ H
    simpa only [mul_assoc] using hrel
  · intro hcore omega
    refine Quotient.inductionOn omega fun x => ?_
    rw [pointRightCosetMul_mk]
    apply Eq.symm
    apply Quotient.sound
    change QuotientGroup.rightRel H x (x * g)
    rw [QuotientGroup.rightRel_apply]
    have hx := Subgroup.mem_iInf.mp hcore x
    change x * g * x⁻¹ ∈ H at hx
    simpa only [mul_assoc] using hx


end CFSG.ProperTwoGeneratedCore
