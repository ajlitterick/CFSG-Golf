module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.H13.U3SimpleRoot
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneRoot

public section

namespace CFSG.Quasithin.SteinbergBY

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem card_statedProj_statedSU_three_two {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ f) K)) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) / Nat.gcd 3 (2 ^ f + 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK (by norm_num),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : (((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ f) ^ 2 - 1 := by
    have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show ((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((2 ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]; ring]
    exact Int.toNat_natCast _
  have h3 : (((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ f) ^ 3 + 1 := by
    rw [show ((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((2 ^ f) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3]

theorem exists_prime_five_le_dvd_sq_sub_one {q : ℕ} (hq : 4 ≤ q) (hev : Even q) :
    ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ q ^ 2 - 1 := by
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q := by omega
    zify [this, Nat.one_le_pow 2 q (by omega)]
    ring
  obtain ⟨k, hk⟩ := hev
  obtain ⟨m, hm3, hmodd, hm, hdvd⟩ : ∃ m, 3 ≤ m ∧ m % 2 = 1 ∧ m % 3 ≠ 0 ∧
      m ∣ q ^ 2 - 1 := by
    rw [hsq]
    by_cases h3 : (q - 1) % 3 = 0
    · exact ⟨q + 1, by omega, by omega, by omega, dvd_mul_left _ _⟩
    · exact ⟨q - 1, by omega, by omega, h3, dvd_mul_right _ _⟩
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  refine ⟨m.minFac, hp, ?_, (Nat.minFac_dvd m).trans hdvd⟩
  have h2 : m.minFac ≠ 2 := fun h => by
    have := Nat.minFac_dvd m
    rw [h] at this
    omega
  have h3 : m.minFac ≠ 3 := fun h => by
    have := Nat.minFac_dvd m
    rw [h] at this
    omega
  have h4 : m.minFac ≠ 4 := fun h => by
    rw [h] at hp
    exact absurd hp (by decide)
  have := hp.two_le
  omega

theorem card_PSU3_arith {K : Type} [Field K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ r : ℕ, Nat.card (StatedProj (StatedSU 3 (2 ^ f) K)) = (2 ^ f) ^ 3 * r ∧ Odd r ∧
      ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ r := by
  set q := 2 ^ f with hqdef
  have hq4 : 4 ≤ q := by
    rw [hqdef]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqev : Even q := by
    rw [hqdef]
    exact (Nat.even_pow' (by omega)).mpr even_two
  set m := (q ^ 2 - 1) * (q ^ 3 + 1) with hmdef
  set g := Nat.gcd 3 (q + 1) with hgdef
  have hgm : g ∣ m := (Nat.gcd_dvd_right 3 (q + 1)).trans (Dvd.dvd.mul_left (by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)) _)
  refine ⟨m / g, ?_, ?_, ?_⟩
  · rw [card_statedProj_statedSU_three_two (by omega) hK, Nat.mul_div_assoc _ hgm]
  · have hmodd : Odd m := by
      have hq2 : Even (q ^ 2) := (Nat.even_pow' (by norm_num)).mpr hqev
      have hq3 : Even (q ^ 3) := (Nat.even_pow' (by norm_num)).mpr hqev
      have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [hmdef, Nat.odd_mul]
      obtain ⟨a, ha⟩ := hq2
      obtain ⟨b, hb⟩ := hq3
      exact ⟨⟨a - 1, by omega⟩, ⟨b, by omega⟩⟩
    exact Odd.of_dvd_nat hmodd (Nat.div_dvd_of_dvd hgm)
  · obtain ⟨p, hp, hp5, hpq⟩ := exists_prime_five_le_dvd_sq_sub_one hq4 hqev
    refine ⟨p, hp, hp5, ?_⟩
    have hpg : Nat.Coprime p g := Nat.coprime_of_dvd' fun r hr hrp hrg => by
      have h3 : r ∣ 3 := hrg.trans (Nat.gcd_dvd_left 3 (q + 1))
      have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
      have : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
      omega
    have hpm : p ∣ m / g * g := by
      rw [Nat.div_mul_cancel hgm, hmdef]
      exact Dvd.dvd.mul_right hpq _
    exact hpg.dvd_of_dvd_mul_right hpm


end CFSG.Quasithin.SteinbergBY
