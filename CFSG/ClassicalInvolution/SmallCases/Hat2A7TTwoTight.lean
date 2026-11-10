module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TZStar

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section TwoGroup

variable {F : Type} [Group F] [Finite F]

theorem le_centralizer_of_two_group_normalizes {J : Subgroup F} {t : F}
    (hJ : IsClassical2A7 ⊤ J t) (P1 : classicalInvolutionOddCore ↥J ≤ Subgroup.center ↥J)
    {R : Subgroup F} (hRN : R ≤ Subgroup.normalizer (J : Set F)) (hR2 : IsPGroup 2 R)
    (hcard : 4 < Nat.card R) {z : F} (hzR : z ∈ R)
    (huniq : ∀ x ∈ R, orderOf x = 2 → x = z) : J ≤ Subgroup.centralizer ({z} : Set F) := by
  have htriv := oddQuotAut_conjOn_eq_one_of_card hJ.witness hRN hR2 hzR huniq hcard
  have hzc := centralizes_of_oddQuotAut_eq_one hJ.perfect P1 (hRN hzR) htriv
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hzc k hk

theorem two_subgroup_unique_involution {N : Subgroup F} {z : F} (hN : IsClassical2A7 ⊤ N z)
    {R : Subgroup F} (hRN : R ≤ N) (hR2 : IsPGroup 2 R) (hcard : 4 < Nat.card R) :
    z ∈ R ∧ ∀ x ∈ R, orderOf x = 2 → x = z := by
  have huniq : ∀ x ∈ R, orderOf x = 2 → x = z := fun x hx hx2 =>
    hN.eq_of_orderOf_eq_two (hRN hx) hx2
  refine ⟨?_, huniq⟩
  have hdvd : 2 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk] at hcard ⊢
    have : k ≠ 0 := by
      rintro rfl
      simp at hcard
    exact dvd_pow_self 2 this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxz : (x : F) = z := huniq x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
  rw [← hxz]
  exact x.2

end TwoGroup

section TwoTight

variable {F : Type} [Group F] [Finite F]


omit [Finite F] in
theorem isPGroup_zpowers_of_orderOf_eq_two {u : F} (hu : orderOf u = 2) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; simp)


end TwoTight

end CFSG.ClassicalInvolution.Hat2A7T
