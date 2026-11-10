module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

theorem card_sl2_eq {F : Type} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]


theorem sixteen_dvd_pow_four_sub_one (a : ℕ) (ha : Odd a) : 16 ∣ (a * a) ^ 2 - 1 := by
  have h2 : a % 2 = 1 := Nat.odd_iff.mp ha
  have hpos : 1 ≤ (a * a) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
  have h1 : (a * a) ^ 2 % 16 = 1 := by
    have : a % 16 = 1 ∨ a % 16 = 3 ∨ a % 16 = 5 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 11 ∨
        a % 16 = 13 ∨ a % 16 = 15 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, Nat.mul_mod, h]
  exact (Nat.modEq_iff_dvd' hpos).mp (by unfold Nat.ModEq; omega)

theorem odd_of_factorization_two_eq_three {p f : ℕ} (hodd : Odd p)
    (h : (p ^ f * ((p ^ f) ^ 2 - 1)).factorization 2 = 3) : Odd f := by
  by_contra hfe
  rw [Nat.not_odd_iff_even] at hfe
  obtain ⟨g, hg⟩ := hfe
  have haodd : Odd (p ^ g) := hodd.pow
  have hq : p ^ f = p ^ g * p ^ g := by rw [hg, pow_add]
  have hne : p ^ f * ((p ^ f) ^ 2 - 1) ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have h16 : 16 ∣ (p ^ g * p ^ g) ^ 2 - 1 := sixteen_dvd_pow_four_sub_one _ haodd
  have hdvd : 2 ^ 4 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [hq]
    exact Dvd.dvd.mul_left (by norm_num; exact h16) _
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  omega


end CFSG.ClassicalInvolution.Asc77.T3CII
