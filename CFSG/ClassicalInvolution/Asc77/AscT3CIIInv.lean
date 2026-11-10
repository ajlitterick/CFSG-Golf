module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIISl2
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC4

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Twin

variable {G : Type} [Group G] {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F))
include hodd

theorem equiv_sl2_apply_eq_neg_one {K : Subgroup G} {z : G} (e : K ≃* SL(2, F))
    (hz : IsUniqueInvolution K z) : e ⟨z, hz.mem⟩ = -1 := by
  have h2 : orderOf (⟨z, hz.mem⟩ : K) = 2 := by
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    rw [Subgroup.orderOf_mk]
    exact this
  have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp h2
  rw [this]
  simp

variable {K K' : Subgroup G} {z : G}

theorem eq_one_or_eq_of_central (e : K ≃* SL(2, F)) (hz : IsUniqueInvolution K z) {c : G}
    (hc : c ∈ K) (hcc : ∀ y ∈ K, c * y = y * c) : c = 1 ∨ c = z := by
  have hcen : (⟨c, hc⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcc y y.2).symm
  have h1 := (mem_center_iff_of_equiv_sl2 e _).mp hcen
  rcases (mem_center_sl2_iff _).mp h1 with h | h
  · left
    have : (⟨c, hc⟩ : K) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have h2 : e ⟨c, hc⟩ = e ⟨z, hz.mem⟩ := by rw [h, equiv_sl2_apply_eq_neg_one hodd e hz]
    exact congrArg Subtype.val (e.injective h2)


end Twin

end CFSG.ClassicalInvolution.Asc77.T3CII
