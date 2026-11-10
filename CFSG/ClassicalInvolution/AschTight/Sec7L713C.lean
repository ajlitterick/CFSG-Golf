module

public import CFSG.ClassicalInvolution.Asc77.AscIHSL2
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]


theorem mem_or_mul_inv_mem_of_relIndex_two {A R : Subgroup G} (h2 : A.relIndex R = 2) {x y : G}
    (hx : x ∈ R) (hxA : x ∉ A) (hy : y ∈ R) : y ∈ A ∨ y * x⁻¹ ∈ A := by
  have hidx : (A.subgroupOf R).index = 2 := h2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : ↥R))
    (b := (⟨x, hx⟩ : ↥R)⁻¹)
  rw [inv_mem_iff] at key
  by_cases hyA : y ∈ A
  · exact Or.inl hyA
  · right
    have hxA' : (⟨x, hx⟩ : ↥R) ∉ A.subgroupOf R := fun h => hxA (Subgroup.mem_subgroupOf.mp h)
    have hyA' : (⟨y, hy⟩ : ↥R) ∉ A.subgroupOf R := fun h => hyA (Subgroup.mem_subgroupOf.mp h)
    have h1 : (⟨y, hy⟩ : ↥R) * (⟨x, hx⟩ : ↥R)⁻¹ ∈ A.subgroupOf R := key.mpr (iff_of_false hyA' hxA')
    exact Subgroup.mem_subgroupOf.mp h1

theorem mul_self_mem_of_relIndex_two {A R : Subgroup G} (h2 : A.relIndex R = 2) {x : G}
    (hx : x ∈ R) : x * x ∈ A := by
  have hidx : (A.subgroupOf R).index = 2 := h2
  exact Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx ⟨x, hx⟩)

theorem relIndex_eq_two_of_card [Finite G] {A R : Subgroup G} (hAR : A ≤ R)
    (hcard : Nat.card R = 2 * Nat.card A) : A.relIndex R = 2 := by
  have h1 := Subgroup.relIndex_mul_card A R
  rw [inf_eq_left.mpr hAR, hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
