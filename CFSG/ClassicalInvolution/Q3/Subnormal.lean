module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem commutator_le_of_isSubnormal {p : ℕ} (hp : p.Prime) {J H N P : Subgroup G}
    (hJ : IsSubnormal J H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hcop : ¬ p ∣ Nat.card N) (hPJ : P ≤ J) (hP : IsPGroup p P) : ⁅N, P⁆ ≤ J := by
  induction hJ generalizing P with
  | @refl K =>
    have hHN : K ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hPJ.trans hHN)).trans hNH
  | @step J M H hJM hJn hMH ih =>
    have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
    have hMH' : M ≤ H := isSubnormal_le hMH
    have hPM : P ≤ M := hPJ.trans hJM
    have h1 : ⁅N, P⁆ ≤ M := ih hNH hN hPM hP
    have hPnorm : P ≤ Subgroup.normalizer (N : Set G) := fun x hx => hHN (hMH' (hPM hx))
    have hA : ⁅⁅N, P⁆, P⁆ ≤ J := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      have haM : a ∈ M := h1 ha
      have hxJ : x ∈ J := hPJ hx
      have hconj : a * x * a⁻¹ ∈ J :=
        (Subgroup.normal_subgroupOf_iff hJM).mp hJn x a hxJ haM
      rw [commutatorElement_def]
      have := J.mul_mem hconj (J.inv_mem hxJ)
      simpa [mul_assoc] using this
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp P N hP hcop
      hPnorm] at hA
    exact hA


theorem not_three_dvd_card_of_isPGroup_two {U : Subgroup G} (hU : IsPGroup 2 U) :
    ¬ 3 ∣ Nat.card U := by
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  intro h
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  omega


end CFSG.ClassicalInvolution.Q3
