module

public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

section Commutators

variable {E : Type*} [Group E]

theorem commute_commutatorElement_of_mem_center {a x y : E} (hx : ⁅a, x⁆ ∈ center E)
    (hy : ⁅a, y⁆ ∈ center E) : a * ⁅x, y⁆ = ⁅x, y⁆ * a := by
  have hx' : a * x * a⁻¹ = x * ⁅a, x⁆ := by
    rw [mem_center_iff.mp hx x, commutatorElement_def]
    group
  have hy' : a * y * a⁻¹ = y * ⁅a, y⁆ := by
    rw [mem_center_iff.mp hy y, commutatorElement_def]
    group
  have key : a * ⁅x, y⁆ * a⁻¹ = ⁅x, y⁆ := by
    have h : a * ⁅x, y⁆ * a⁻¹ = ⁅a * x * a⁻¹, a * y * a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h, hx', hy', CentralExtensions.commutator_mul_center_left _ _ _ hx,
      CentralExtensions.commutator_mul_center_right _ _ _ hy]
  calc a * ⁅x, y⁆ = a * ⁅x, y⁆ * a⁻¹ * a := by group
    _ = ⁅x, y⁆ * a := by rw [key]


end Commutators

section Norm


end Norm

section Lift


end Lift

end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
