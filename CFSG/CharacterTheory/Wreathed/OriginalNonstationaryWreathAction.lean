module

public import CFSG.CharacterTheory.Wreathed.OriginalCoveringSylowNormalizer

public noncomputable section

namespace CFSG.Wreathed.OriginalNonstationaryWreathAction

open scoped Classical

universe u

variable {G : Type u} [Group G]

theorem central_involution_mem_normal_two_subgroup [Finite G]
    [IsCyclic (Subgroup.center G)] (hG : IsPGroup 2 G)
    (x : G) (hx : x ∈ Subgroup.center G) (horder : orderOf x = 2)
    (D : Subgroup G) [D.Normal] (hD : D ≠ ⊥) : x ∈ D := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent G := hG.isNilpotent
  let L := D ⊓ Subgroup.center G
  have hL : L ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hD
  have hcard : Nat.card L ≠ 1 := by
    intro h
    exact hL ((Subgroup.eq_bot_iff_card L).mpr h)
  have hdvd : 2 ∣ Nat.card L := (hG.to_subgroup L).card_eq_or_dvd.resolve_left hcard
  let xZ : Subgroup.center G := ⟨x, hx⟩
  have hle : Subgroup.zpowers xZ ≤ L.subgroupOf (Subgroup.center G) := by
    apply IsCyclic.subgroup_le_iff_card_dvd.mpr
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe xZ, horder,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hdvd
  exact (hle (Subgroup.mem_zpowers xZ)).1


theorem original_sylow_center_isCyclic (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (Subgroup.center (S : Subgroup G)) := by
  let F : Subgroup.center (S : Subgroup G) ≃* Original.Z (2 ^ n) :=
    (e.subgroupMap (Subgroup.center (S : Subgroup G))).trans
      (MulEquiv.subgroupCongr ((Subgroup.map_center_eq e).trans
        (wreath_center_involution_and_quaternion_coordinates n hn).center))
  apply F.isCyclic.mpr
  change IsCyclic (Subgroup.zpowers (Original.a (2 ^ n)))
  infer_instance

theorem original_involution_mem_normal_sylow_subgroup [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (D : Subgroup (S : Subgroup G)) [D.Normal] (hD : D ≠ ⊥) :
    e.symm (Original.x (2 ^ n)) ∈ D := by
  let : IsCyclic (Subgroup.center (S : Subgroup G)) :=
    original_sylow_center_isCyclic n hn S e
  apply central_involution_mem_normal_two_subgroup S.isPGroup'
    (e.symm (Original.x (2 ^ n))) ?_ ?_ D hD
  · rw [← Subgroup.map_center_eq e.symm]
    refine Subgroup.mem_map.mpr ⟨Original.x (2 ^ n), ?_, rfl⟩
    rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _
  · exact (e.symm.orderOf_eq _).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1


open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalCoveringSylowNormalizer


theorem centralizer_map_subtype (K : Subgroup G) (A : Subgroup K) :
    (Subgroup.centralizer ((A.map K.subtype) : Set G)).subgroupOf K =
      Subgroup.centralizer (A : Set K) := by
  ext k
  change (k : G) ∈ Subgroup.centralizer ((A.map K.subtype) : Set G) ↔ _
  constructor
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hk (a : G)
      (Subgroup.mem_map_of_mem K.subtype ha))
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨aK, haK, heq⟩ := Subgroup.mem_map.mp ha
    rw [← heq]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk aK haK)


end CFSG.Wreathed.OriginalNonstationaryWreathAction
