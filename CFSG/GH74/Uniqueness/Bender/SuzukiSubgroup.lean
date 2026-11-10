module

public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Complement

variable {K : Type*} [Group K] [Finite K]


end Complement

section Eight

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.suzuki_eight_solvable_card
    {e : ℕ} (h : BenderType K 3 2 e) {J : Subgroup K}
    [Group.IsSolvable J] (h7 : 7 ∣ Nat.card J) (h2 : 2 ∣ Nat.card J) (h4 : ¬ 4 ∣ Nat.card J) :
    Nat.card J = 14 := by
  classical
  have he : e = 1 := h.e_eq_one_of_two
  subst he
  have hJ1 : J ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h7
    omega
  obtain ⟨m, hm⟩ := h7
  rcases h.suzuki_solvable_subgroup hJ1 with ⟨Q, hJQ⟩ | ⟨x, hx1, hxodd, hJN⟩
  · obtain ⟨t, hc⟩ := h.exists_benderCore Q
    have hdvd : Nat.card J ∣ Nat.card (borel (Q : Subgroup K)) := Subgroup.card_dvd_of_le hJQ
    rw [hc.card_borel] at hdvd
    norm_num at hdvd
    have hm64 : m ∣ 64 := by
      rw [hm] at hdvd
      have : 7 * m ∣ 7 * 64 := by simpa using hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hm64' : m ≤ 64 := Nat.le_of_dvd (by norm_num) hm64
    interval_cases m <;> omega
  · obtain ⟨-, -, hTcard, hNcard⟩ := h.suzuki_odd_centralizer hx1 hxodd
    have hdvd : Nat.card J ∣
        Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) :=
      Subgroup.card_dvd_of_le hJN
    have hT : Nat.card (centralizer ({x} : Set K)) = 7 ∨ Nat.card (centralizer ({x} : Set K)) = 5 ∨
        Nat.card (centralizer ({x} : Set K)) = 13 := by
      rcases hTcard with h1 | ⟨a, hn, h2 | h3⟩
      · left
        rw [h1]
        norm_num
      · have ha : a = 1 := by omega
        subst ha
        right
        left
        rw [h2]
        norm_num
      · have ha : a = 1 := by omega
        subst ha
        right
        right
        rw [h3]
        norm_num
    have hpos : 0 < Nat.card J := Nat.card_pos
    have h7N : 7 ∣ Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) :=
      (Dvd.intro _ hm.symm).trans hdvd
    have hleN := Nat.le_of_dvd Nat.card_pos hdvd
    rcases hNcard with h1 | h1 <;> rcases hT with h3 | h3 | h3 <;> rw [h1, h3] at h7N hleN <;>
      omega

end Eight

end CFSG.GH74.Uniqueness.Bender
