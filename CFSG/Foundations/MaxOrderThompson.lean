module

public import CFSG.GroupTheory.ThompsonIsomorphism
public import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.RankThree.PGroups.ZJCenterIntersection
public import CFSG.Foundations.MaxCardThompson
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

open Subgroup

universe u v

section General

variable {G : Type u} [Group G]


theorem le_orderThompson {A : Subgroup G} (hA : A ∈ maxOrderAbelianFamily G) :
    A ≤ orderThompson G :=
  le_sSup hA


instance orderZJ_isMulCommutative : IsMulCommutative (orderZJ G) := by
  unfold orderZJ
  infer_instance

theorem map_mem_maxOrderAbelianFamily {H : Type v} [Group H] (e : G ≃* H) {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : A.map e.toMonoidHom ∈ maxOrderAbelianFamily H :=
  image_maxOrderAbelianFamily e ▸ ⟨A, hA, rfl⟩

instance orderThompson_characteristic : (orderThompson G).Characteristic :=
  characteristic_iff_map_eq.mpr map_orderThompson

instance orderZJ_characteristic : (orderZJ G).Characteristic :=
  characteristic_iff_map_eq.mpr map_orderZJ


instance ambientOrderZJ_isMulCommutative (S : Subgroup G) :
    IsMulCommutative (ambientOrderZJ S) := by
  unfold ambientOrderZJ
  infer_instance

theorem normalizer_le_normalizer_ambientOrderZJ (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (ambientOrderZJ S : Set G) :=
  normalizer_le_normalizer_image_of_characteristic S (orderZJ S)


end General

section Finite

variable {G : Type u} [Group G] [Finite G]


theorem card_le_maxAbelianOrder_of_isMulCommutative {A : Subgroup G} (hA : IsMulCommutative A) :
    Nat.card A ≤ maxAbelianOrder G :=
  RankThree.PGroups.card_le_maxAbelianOrder hA

theorem maxOrderAbelianFamily_nonempty : (maxOrderAbelianFamily G).Nonempty :=
  RankThree.PGroups.exists_mem_maxOrderAbelianFamily

theorem isMaxCardAbelian_iff_mem_maxOrderAbelianFamily {A : Subgroup G} :
    IsMaxCardAbelian A ↔ A ∈ maxOrderAbelianFamily G := by
  constructor
  · rintro ⟨hA, hmax⟩
    refine ⟨hA, le_antisymm (card_le_maxAbelianOrder_of_isMulCommutative hA) ?_⟩
    obtain ⟨B, hB, hcard⟩ := maxOrderAbelianFamily_nonempty (G := G)
    exact hcard ▸ hmax B hB
  · rintro ⟨hA, hcard⟩
    exact ⟨hA, fun B hB => hcard ▸ card_le_maxAbelianOrder_of_isMulCommutative hB⟩

theorem setOf_isMaxCardAbelian_eq :
    {A : Subgroup G | IsMaxCardAbelian A} = maxOrderAbelianFamily G :=
  Set.ext fun _ => isMaxCardAbelian_iff_mem_maxOrderAbelianFamily

theorem maxCardThompson_eq_orderThompson : maxCardThompson G = orderThompson G := by
  unfold maxCardThompson orderThompson
  rw [setOf_isMaxCardAbelian_eq]

theorem maxCardZJ_eq_orderZJ : maxCardZJ G = orderZJ G := by
  unfold maxCardZJ orderZJ
  rw [maxCardThompson_eq_orderThompson]

theorem mem_maxOrderAbelianFamily_iff_forall_card_le {A : Subgroup G} :
    A ∈ maxOrderAbelianFamily G ↔
      IsMulCommutative A ∧ ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ Nat.card A :=
  isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.symm

theorem eq_of_mem_maxOrderAbelianFamily_of_le {A B : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) (hB : IsMulCommutative B) (hAB : A ≤ B) : A = B :=
  eq_of_le_of_card_ge hAB (hA.2 ▸ card_le_maxAbelianOrder_of_isMulCommutative hB)

theorem mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) {x : G} (hx : x ∈ centralizer (A : Set G)) : x ∈ A := by
  have hAx := eq_of_mem_maxOrderAbelianFamily_of_le hA
    (RankThree.PGroups.isMulCommutative_sup_zpowers hA.1 hx) le_sup_left
  rw [hAx]
  exact mem_sup_right (mem_zpowers x)

theorem centralizer_eq_self_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : centralizer (A : Set G) = A :=
  le_antisymm (fun _ hx => mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily hA hx)
    (le_centralizer_iff_isMulCommutative.mpr hA.1)

theorem center_le_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : center G ≤ A :=
  fun _ hx => mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily hA (center_le_centralizer _ hx)

theorem orderZJ_eq_sInf : orderZJ G = sInf (maxOrderAbelianFamily G) :=
  RankThree.PGroups.zj_center_intersection

theorem orderZJ_eq_iInf : orderZJ G = ⨅ A ∈ maxOrderAbelianFamily G, A := by
  rw [orderZJ_eq_sInf, sInf_eq_iInf]

theorem orderZJ_eq_iInf_subtype :
    orderZJ G = ⨅ A : maxOrderAbelianFamily G, (A : Subgroup G) := by
  rw [orderZJ_eq_sInf, sInf_eq_iInf']

theorem orderZJ_le_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : orderZJ G ≤ A := by
  rw [orderZJ_eq_sInf]
  exact sInf_le hA

theorem mem_orderZJ_iff {x : G} : x ∈ orderZJ G ↔ ∀ A ∈ maxOrderAbelianFamily G, x ∈ A := by
  rw [orderZJ_eq_sInf, mem_sInf]


theorem center_le_orderZJ_of_finite : center G ≤ orderZJ G := by
  rw [orderZJ_eq_sInf]
  exact le_sInf fun _ hA => center_le_of_mem_maxOrderAbelianFamily hA

theorem orderZJ_ne_bot_of_isPGroup [Nontrivial G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G) :
    orderZJ G ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  intro hbot
  have hcenter : center G = ⊥ := le_bot_iff.mp (hbot ▸ center_le_orderZJ_of_finite)
  exact hG.bot_lt_center.ne hcenter.symm


theorem map_subtype_mem_maxOrderAbelianFamily {H M : Subgroup G}
    (hM : M ∈ maxOrderAbelianFamily G) (hMH : M ≤ H) {B : Subgroup H}
    (hB : B ∈ maxOrderAbelianFamily H) : B.map H.subtype ∈ maxOrderAbelianFamily G :=
  isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp
    ((isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr hM).map_subtype hMH
      (isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr hB))


theorem orderZJ_le_ambientOrderZJ {H M : Subgroup G} (hM : M ∈ maxOrderAbelianFamily G)
    (hMH : M ≤ H) : orderZJ G ≤ ambientOrderZJ H := by
  intro x hx
  have hxH : x ∈ H := hMH (orderZJ_le_of_mem_maxOrderAbelianFamily hM hx)
  refine ⟨⟨x, hxH⟩, mem_orderZJ_iff.mpr fun B hB => ?_, rfl⟩
  obtain ⟨y, hy, hyx⟩ := orderZJ_le_of_mem_maxOrderAbelianFamily
    (map_subtype_mem_maxOrderAbelianFamily hM hMH hB) hx
  have : y = ⟨x, hxH⟩ := Subtype.ext hyx
  exact this ▸ hy

end Finite


section Products


end Products


end CFSG
