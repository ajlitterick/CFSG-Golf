module

public import CFSG.Quasithin.Recognition.GoldschmidtCompletion

public section

universe u

namespace CFSG.Quasithin

open Monoid


namespace GoldAmalgam

@[expose] def ofSubgroupPair {D : Type*} [Group D] (A B : Subgroup D) :
    GoldAmalgam A (A ⊓ B : Subgroup D) B where
  toA := Subgroup.inclusion inf_le_left
  toB := Subgroup.inclusion inf_le_right
  toA_injective := Subgroup.inclusion_injective _
  toB_injective := Subgroup.inclusion_injective _

@[expose] def ofSubgroupPair_completion {D : Type*} [Group D] (A B : Subgroup D)
    (hgen : A ⊔ B = ⊤) : GoldCompletion (ofSubgroupPair A B) D where
  ψA := A.subtype
  ψB := B.subtype
  ψA_injective := A.subtype_injective
  ψB_injective := B.subtype_injective
  comm _ := rfl
  gen := by rw [Subgroup.range_subtype, Subgroup.range_subtype, hgen]
  inter := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    intro d hd
    exact ⟨⟨d, hd⟩, rfl⟩

theorem ofSubgroupPair_edgeA_index {D : Type*} [Group D] (A B : Subgroup D) :
    (ofSubgroupPair A B).edgeA.index = (A ⊓ B).relIndex A := by
  unfold edgeA ofSubgroupPair
  rw [Subgroup.inclusion_range]
  rfl

theorem ofSubgroupPair_edgeB_index {D : Type*} [Group D] (A B : Subgroup D) :
    (ofSubgroupPair A B).edgeB.index = (A ⊓ B).relIndex B := by
  unfold edgeB ofSubgroupPair
  rw [Subgroup.inclusion_range]
  rfl

theorem ofSubgroupPair_isFaithful_iff {D : Type*} [Group D] (A B : Subgroup D) (hgen : A ⊔ B = ⊤) :
    (ofSubgroupPair A B).IsFaithful ↔ ∀ N : Subgroup D, N.Normal → N ≤ A ⊓ B → N = ⊥ := by
  rw [(ofSubgroupPair_completion A B hgen).isFaithful_iff]
  have hedge : (ofSubgroupPair_completion A B hgen).edge = A ⊓ B := by
    rw [GoldCompletion.edge_eq_inf]
    simp [ofSubgroupPair_completion]
  rw [hedge]

end GoldAmalgam


end CFSG.Quasithin
