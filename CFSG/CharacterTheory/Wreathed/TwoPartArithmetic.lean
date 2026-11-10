module

public import CFSG.CharacterTheory.Wreathed.Coordinates

public section

namespace CFSG.Wreathed

theorem two_factorization_eq_one_of_mod_four (a : ℕ) (ha : a % 4 = 2) :
    a.factorization 2 = 1 := by
  have ha0 : a ≠ 0 := by omega
  have h2 : 2 ^ 1 ∣ a := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h4 : ¬2 ^ 2 ∣ a := by
    intro h
    have hzero := Nat.dvd_iff_mod_eq_zero.mp h
    norm_num at hzero
    omega
  have hlo := (Nat.prime_two.pow_dvd_iff_le_factorization ha0).mp h2
  have hhi : ¬2 ≤ a.factorization 2 := by
    intro h
    exact h4 ((Nat.prime_two.pow_dvd_iff_le_factorization ha0).mpr h)
  omega


theorem two_part_square_sub_one_split (q n : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 1)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q - 1).factorization 2 = n := by
  have hqm : q - 1 ≠ 0 := by omega
  have hqp : q + 1 ≠ 0 := by omega
  have hlow := two_factorization_eq_one_of_mod_four (q + 1) (by omega)
  have hfac : (q ^ 2 - 1).factorization 2 = (q - 1).factorization 2 + 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1,
      Nat.factorization_mul hqp hqm]
    simp only [Finsupp.add_apply, hlow]
    omega
  have hexp : (q ^ 2 - 1).factorization 2 = n + 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    simpa only [pow_succ, Nat.mul_comm] using hpart
  omega

theorem two_part_square_sub_one_nonsplit (q n : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 3)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q + 1).factorization 2 = n := by
  have hqm : q - 1 ≠ 0 := by omega
  have hqp : q + 1 ≠ 0 := by omega
  have hlow := two_factorization_eq_one_of_mod_four (q - 1) (by omega)
  have hfac : (q ^ 2 - 1).factorization 2 = (q + 1).factorization 2 + 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1,
      Nat.factorization_mul hqp hqm]
    simp only [Finsupp.add_apply, hlow]
  have hexp : (q ^ 2 - 1).factorization 2 = n + 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    simpa only [pow_succ, Nat.mul_comm] using hpart
  omega


end CFSG.Wreathed
