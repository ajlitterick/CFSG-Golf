module

public import CFSG.Milestones.ASVolI.A3L3.Defs
public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.ASVolI

open scoped Pointwise

theorem burnsideA315y_inf_eq_bot_of_odd {X : Type} [Group X] [Finite X] {B S : Subgroup X}
    (hBodd : Odd (Nat.card ↥B)) (hS : IsPGroup 2 ↥S) : B ⊓ S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdB : Nat.card ↥(B ⊓ S) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_left
  have hdS : Nat.card ↥(B ⊓ S) ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card ↥B) (2 ^ k) :=
    (Nat.coprime_two_left.2 hBodd).symm.pow_right k
  have h1 : Nat.card ↥(B ⊓ S) ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdB hdS
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)

theorem burnsideA315y_relIndex_sup {X : Type} [Group X] [Finite X] {B S : Subgroup X}
    (hBodd : Odd (Nat.card ↥B)) (hS : IsPGroup 2 ↥S)
    (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) :
    B.relIndex (B ⊔ S) = Nat.card ↥S := by
  have hcard : Nat.card ↥(B ⊔ S) = Nat.card ↥B * Nat.card ↥S :=
    burnsideA315x_card_sup hperm (burnsideA315y_inf_eq_bot_of_odd hBodd hS)
  have h := Subgroup.relIndex_mul_card B (B ⊔ S)
  rw [inf_of_le_left le_sup_left, hcard] at h
  have hB0 : 0 < Nat.card ↥B := Nat.card_pos
  rw [mul_comm (Nat.card ↥B)] at h
  exact Nat.eq_of_mul_eq_mul_right hB0 h

theorem burnsideA315y_le_of_odd {X : Type} [Group X] [Finite X] {B S N : Subgroup X}
    (hBodd : Odd (Nat.card ↥B)) (hS : IsPGroup 2 ↥S)
    (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X))
    (hN : N ≤ B ⊔ S) (hBN : B ≤ Subgroup.normalizer (N : Set X)) (hNodd : Odd (Nat.card ↥N)) :
    N ≤ B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have h1 : B.relIndex (B ⊔ S) = 2 ^ k := hk ▸ burnsideA315y_relIndex_sup hBodd hS hperm
  have h2 : B.relIndex (N ⊔ B) = B.relIndex N := burnsideA315x_relIndex_sup hBN
  have h3 : B.relIndex N ∣ Nat.card ↥N := Subgroup.relIndex_dvd_card B N
  have h4 : B.relIndex (N ⊔ B) ∣ B.relIndex (B ⊔ S) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex B (N ⊔ B) (B ⊔ S) le_sup_right
      (sup_le hN le_sup_left))
  have hodd : Odd (B.relIndex (N ⊔ B)) := h2 ▸ Odd.of_dvd_nat hNodd h3
  have hcop : Nat.Coprime (B.relIndex (N ⊔ B)) (2 ^ k) :=
    (Nat.coprime_two_right.2 hodd).pow_right k
  have h5 : B.relIndex (N ⊔ B) = 1 := Nat.Coprime.eq_one_of_dvd hcop (h1 ▸ h4)
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 h5)

theorem burnsideA315y_sup_solvable {X : Type} [Group X] [Finite X] {B S : Subgroup X}
    (hBab : IsMulCommutative ↥B) (hBodd : Odd (Nat.card ↥B)) (hS : IsPGroup 2 ↥S)
    (hperm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) :
    Group.IsSolvable ↥(B ⊔ S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBle : B ≤ B ⊔ S := le_sup_left
  have hle : S ≤ B ⊔ S := le_sup_right
  have eA : ↥(B.subgroupOf (B ⊔ S)) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBle
  have eC : ↥(S.subgroupOf (B ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hle
  haveI : Group.IsNilpotent ↥B := inferInstance
  refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf (B ⊔ S))
    (S.subgroupOf (B ⊔ S)) (Group.nilpotent_of_mulEquiv eA.symm)
    ((hS.of_equiv eC.symm).isNilpotent) ?_ ?_
  · rw [Nat.card_congr eA.toEquiv, Nat.card_congr eC.toEquiv]
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_left.2 hBodd).symm.pow_right k
  · intro g
    have hg : (g : X) ∈ ((B ⊔ S : Subgroup X) : Set X) := g.2
    rw [burnsideA315x_coe_sup hperm] at hg
    obtain ⟨b, hb, s, hs, hbs⟩ := hg
    exact ⟨⟨b, hBle hb⟩, hb, ⟨s, hle hs⟩, hs, Subtype.ext hbs.symm⟩

theorem burnsideA315y_le_normalizer_map {X : Type*} [Group X] {H : Subgroup X}
    (R : Subgroup ↥H) [R.Normal] : H ≤ Subgroup.normalizer ((R.map H.subtype : Subgroup X) : Set X) := by
  have hle : R.map H.subtype ≤ H := Subgroup.map_subtype_le R
  have heq : (R.map H.subtype).subgroupOf H = R := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI : ((R.map H.subtype).subgroupOf H).Normal := by rw [heq]; infer_instance
  exact Subgroup.le_normalizer_of_normal_subgroupOf hle


end CFSG.ASVolI
