module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem factorization_card_adjointGroup_E8_le_of_dvd_add_one
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization p ≤
      8 * (Nat.card K + 1).factorization p + 1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := fun h => by
    have h1 : p ∣ Nat.card K + 1 - Nat.card K := Nat.dvd_sub hpq h
    rw [show Nat.card K + 1 - Nat.card K = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK1 : ¬ p ∣ Nat.card K - 1 := fun h => by
    have h1 : p ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub hpq h
    rw [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
    have : Fact p.Prime := ⟨hp⟩
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    rw [Nat.cast_add, Nat.cast_one] at h0
    have h1 := orderOf_neg_one (R := ZMod p)
    simp only [ZMod.ringChar_zmod_n, hp2, ite_false] at h1
    rw [eq_neg_of_add_eq_zero_left h0]
    exact h1
  have hsq : (Nat.card K ^ 2 - 1).factorization p = (Nat.card K + 1).factorization p := by
    have h1 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      have : 1 ≤ Nat.card K := by omega
      zify [this, Nat.one_le_pow 2 _ (by omega : 0 < Nat.card K)]
      ring
    rw [h1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpK1, zero_add]
  have hlte : ∀ k : ℕ, k ≠ 0 → p ^ (Nat.card K ^ (2 * k) - 1).factorization p =
      p ^ (Nat.card K + 1).factorization p * p ^ k.factorization p := fun k hk => by
    rw [ordProj_pow_sub_one_of_dvd hp hp2 hpK hq2 hord hk, hsq]
  have h := ordProj_card_adjointGroup_E (τ := Tag.E8) (K := K) (by simp) hp (by omega) hpK
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [hlte 1 one_ne_zero, hlte 4 (by norm_num), hlte 6 (by norm_num), hlte 7 (by norm_num),
    hlte 9 (by norm_num), hlte 10 (by norm_num), hlte 12 (by norm_num), hlte 15 (by norm_num)] at h
  have hnd : ∀ k ∈ ([1, 4, 6, 9, 10, 12, 15] : List ℕ), ¬ p ∣ k := by
    intro k hk hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hle : p ≤ k := Nat.le_of_dvd (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num) hdvd
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals interval_cases p <;> first | omega | (norm_num at hp)
  rw [ordProj_eq_one_of_not_dvd' (hnd 1 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 4 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 6 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 9 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 10 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 12 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 15 (by simp))] at h
  have h7 : (7 : ℕ).factorization p ≤ 1 := by
    rcases eq_or_ne p 7 with rfl | hne
    · rw [Nat.Prime.factorization_self (by norm_num)]
    · rw [Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd)]
      norm_num
  have h' : (Nat.card (adjointGroup Tag.E8 K)).factorization p =
      8 * (Nat.card K + 1).factorization p + (7 : ℕ).factorization p := by
    refine Nat.pow_right_injective hp.two_le ?_
    change p ^ _ = p ^ _
    rw [h]
    ring
  omega

section Twisted


end Twisted

section Family


end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
