module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneInvolutions
public import CFSG.CharacterTheory.TwoRankLowerBound.RankTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

open CFSG.Open CFSG.TwoRankLowerBound.Helpers
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {T : Type*} [Group T] [Finite T]

theorem twoRank_le_one_of_no_four_group
    (hno : ∀ V : Subgroup T, IsElemAbelian 2 V → Nat.card V ≠ 4) :
    twoRank T ≤ 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply csSup_le'
  rintro n ⟨V, _, hV, hcard⟩
  by_contra hn
  have hn' : 2 ≤ n := by omega
  have hbound : 2 ^ 2 ≤ Nat.card V := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide) hn'
  obtain ⟨U, hUcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    Nat.prime_two (IsPGroup.of_card hcard) hbound
  let : IsMulCommutative V := hV.1
  have hU : IsElemAbelian 2 U := by
    refine ⟨inferInstance, ?_⟩
    intro x _
    exact Subtype.ext (hV.2 x.val x.property)
  apply hno (U.map V.subtype) (isElemAbelian_map U hU V.subtype)
  rw [Subgroup.card_map_of_injective V.subtype_injective, hUcard]
  norm_num

theorem involutions_conjugate_of_no_four_group
    (hno : ∀ V : Subgroup T, IsElemAbelian 2 V → Nat.card V ≠ 4)
    (a b : T) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ k : T, k⁻¹ * a * k = b := by
  let S : Sylow 2 T := Classical.choice Sylow.nonempty
  obtain ⟨x, hx⟩ := involution_conjugate_into_sylow S ha
  obtain ⟨y, hy⟩ := involution_conjugate_into_sylow S hb
  have hrank : twoRank (S : Subgroup T) ≤ 1 :=
    (twoRank_subgroup_le _).trans (twoRank_le_one_of_no_four_group hno)
  have hax : orderOf (x⁻¹ * a * x) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj x⁻¹).orderOf_eq a).trans ha
  have hby : orderOf (y⁻¹ * b * y) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj y⁻¹).orderOf_eq b).trans hb
  have heq : x⁻¹ * a * x = y⁻¹ * b * y :=
    congrArg Subtype.val (rank_one_twoGroup_involutions_eq (S : Subgroup T)
      S.isPGroup' hrank ⟨_, hx⟩ ⟨_, hy⟩
      ((Subgroup.orderOf_coe _).symm.trans hax)
      ((Subgroup.orderOf_coe _).symm.trans hby))
  refine ⟨x * y⁻¹, ?_⟩
  calc
    (x * y⁻¹)⁻¹ * a * (x * y⁻¹) = y * (x⁻¹ * a * x) * y⁻¹ := by group
    _ = y * (y⁻¹ * b * y) * y⁻¹ := by rw [heq]
    _ = b := by group


end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
