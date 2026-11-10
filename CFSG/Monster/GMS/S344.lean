module

public import CFSG.Monster.GMS.Extraspecial
public import CFSG.Monster.GMS.Facts.LeechCosets
public import CFSG.Monster.GMS.S31Three
public import CFSG.Monster.GMS.S33
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {d₀ : B}

private theorem isConj_mul_of_not_mem_leechQ
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x)
    (hxQ : x ∉ leechQ w) : IsConj z₀ (x * w) := by
  have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hx2 : orderOf x = 2 := (orderOf_eq_of_isConj hxA).symm.trans hG.1.1
  have hw2 : orderOf w = 2 := (orderOf_eq_of_isConj hw).symm.trans hG.2.1
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hx2
  have hww : w * w = 1 := mul_self_eq_one_of_orderOf hw2
  have hprod : (x * w) * (x * w) = 1 := by
    calc (x * w) * (x * w) = x * (w * x) * w := by group
      _ = x * (x * w) * w := by rw [hxw]
      _ = (x * x) * (w * w) := by group
      _ = 1 := by rw [hxx, hww, one_mul]
  have hne : x * w ≠ 1 := by
    intro h1
    have hxinv : x = w⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right hww] at hxinv
    rw [hxinv] at hxA
    exact hG.not_isConj (hxA.trans hw.symm)
  have hC : x * w ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * w * x = x * (w * x) := by rw [mul_assoc]
      _ = x * (x * w) := by rw [hxw]
  rcases isConj_or_isConj_of_mem_centralizer hSLS hTV hL hG hxA hC
      (orderOf_eq_two_of_mul_self hprod hne) with h | h
  · exact absurd (mem_leechQ_of_isConj_mul hSLS hTV hL hG hxA hw hxw h) hxQ
  · exact h

private theorem two_pow_seventeen_le_card
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) :
    2 ^ 17 ≤ Nat.card ↥(leechQ w ⊓ Subgroup.centralizer ({x} : Set G)) := by
  by_cases hxQ : x ∈ leechQ w
  · have hGw := hG.2.of_isConj hw
    have h1 := hGw.extraspecialData.card_le_two_mul_card_inf_centralizer (le_refl (leechQ w)) hxQ
    rw [hGw.card_leechQ] at h1
    omega
  · have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have := (not_mem_leechQ_of_isConj_mul hSLS hTV hL hG hxA hw hxw
      (isConj_mul_of_not_mem_leechQ hSLS hTV hL hG hw hx hxA hxQ)).2
    omega

theorem s344_card
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y : G} (hw : IsConj z₀ w)
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hxA : IsConj a x) (hyA : IsConj a y) :
    2 ^ 9 ≤ Nat.card ↥(leechQ w ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) := by
  have hQc : Nat.card (leechQ w) = 2 ^ 25 := (hG.2.of_isConj hw).card_leechQ
  have hX := two_pow_seventeen_le_card hSLS hTV hL hG hw hx hxA
  have hY := two_pow_seventeen_le_card hSLS hTV hL hG hw hy hyA
  set Q := leechQ w with hQ
  set A := Subgroup.centralizer ({x} : Set G) with hA
  set B := Subgroup.centralizer ({y} : Set G) with hB
  have hAr := Subgroup.relIndex_mul_card A Q
  have hBr := Subgroup.relIndex_mul_card B Q
  have hABr := Subgroup.relIndex_mul_card (A ⊓ B) Q
  have hle := Subgroup.relIndex_inf_le (H := A) (K := B) (L := Q)
  rw [inf_comm] at hAr hBr
  have hset : A ⊓ B ⊓ Q = Q ⊓ A ⊓ B := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [hset] at hABr
  set N := Nat.card ↥(Q ⊓ A ⊓ B) with hN
  set rA := A.relIndex Q
  set rB := B.relIndex Q
  set rAB := (A ⊓ B).relIndex Q
  have h1 : rA ≤ 2 ^ 8 := by
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ 17) ?_ (by norm_num)
    calc rA * 2 ^ 17 ≤ rA * Nat.card ↥(Q ⊓ A) := Nat.mul_le_mul_left _ hX
      _ = 2 ^ 25 := by rw [hAr, hQc]
      _ = 2 ^ 8 * 2 ^ 17 := by norm_num
  have h2 : rB ≤ 2 ^ 8 := by
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ 17) ?_ (by norm_num)
    calc rB * 2 ^ 17 ≤ rB * Nat.card ↥(Q ⊓ B) := Nat.mul_le_mul_left _ hY
      _ = 2 ^ 25 := by rw [hBr, hQc]
      _ = 2 ^ 8 * 2 ^ 17 := by norm_num
  have h3 : rAB ≤ 2 ^ 16 := by
    calc rAB ≤ rA * rB := hle
      _ ≤ 2 ^ 8 * 2 ^ 8 := Nat.mul_le_mul h1 h2
      _ = 2 ^ 16 := by norm_num
  refine Nat.le_of_mul_le_mul_left (c := 2 ^ 16) ?_ (by norm_num)
  calc 2 ^ 16 * 2 ^ 9 = 2 ^ 25 := by norm_num
    _ = rAB * N := by rw [← hQc, hABr]
    _ ≤ 2 ^ 16 * N := Nat.mul_le_mul_right _ h3

theorem s344_exists
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT4 : TableIVIn G) {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {w x y : G} (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G))
    (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) (hyA : IsConj a y) :
    ∃ w₀ ∈ leechQ w ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      w₀ ≠ w ∧ IsConj z₀ w₀ ∧ IsConj z₀ (w * w₀) := by
  have hQ := (hG.2.of_isConj hw).extraspecialData
  have hXQ : leechQ w ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      leechQ w := inf_le_left.trans inf_le_left
  obtain ⟨E, hEX, hwE, hE8, hE2⟩ :=
    hQ.exists_elementary_card_eight hXQ (s344_card hSLS hTV hL hG hw hx hy hxA hyA)
  obtain ⟨e, heE, he1, heA⟩ := s33 hSLS hTV hL hG hT4 E hE8 hE2
  have heQ : e ∈ leechQ w := hXQ (hEX heE)
  have hew : e ≠ w := fun h => hwE (h ▸ heE)
  have he2 : orderOf e = 2 := orderOf_eq_two_of_mul_self (hE2 e heE) he1
  have heB : IsConj z₀ e := by
    rcases orderOf_eq_two_mem_leechQ hSLS hTV hL hG hw heQ he2 with h | h | h
    · exact absurd h hew
    · exact absurd h heA
    · exact h
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨T₂, T₃, T₄, hT⟩ := (h.leech w hw).exists_orbits
  have he4 : e ∈ T₄ := h.mem_four_of_isConj hw hT heQ hew heB
  have hewB : IsConj z₀ (e * w) :=
    h.isConj_of_mem_four hw hT (hT.four e he4).2.2.2
  refine ⟨e, hEX heE, hew, heB, ?_⟩
  rwa [← hQ.central e heQ]


private theorem eq_one_of_odd_orderOf {w t : G} (ht : t ∈ leechQ w) (hodd : Odd (orderOf t)) :
    t = 1 := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_mem_leechQ ht
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · exfalso
    have : Even (orderOf t) := ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) this


end CFSG.Monster.GMS
