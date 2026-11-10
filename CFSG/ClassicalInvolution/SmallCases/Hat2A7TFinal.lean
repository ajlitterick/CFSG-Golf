module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TReduce
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RCore

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscFusion

section Normalizing

variable {F : Type} [Group F] [Finite F]

theorem exists_orderOf_four_of_two_group {R : Subgroup F} {u : F} (hR2 : IsPGroup 2 R)
    (hu2 : orderOf u = 2) (hcard : 2 < Nat.card R) (huniq : ∀ x ∈ R, orderOf x = 2 → x = u) :
    ∃ a ∈ R, orderOf a = 4 := by
  by_contra hcon
  push Not at hcon
  have hsub : ∀ x ∈ R, x = 1 ∨ x = u := by
    intro x hx
    obtain ⟨k, hk⟩ := hR2.exists_orderOf_eq_pow (⟨x, hx⟩ : R)
    rw [Subgroup.orderOf_mk] at hk
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k
      · left
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hk
      · right
        rw [pow_one] at hk
        exact huniq x hx hk
    · exfalso
      have h4 : 4 ≤ orderOf x := by
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
      obtain ⟨j, hj⟩ := exists_pow_orderOf_eq_four (y := x)
        (hR2.to_le (Subgroup.zpowers_le.mpr hx)) h4
      exact hcon (x ^ j) (R.pow_mem hx j) hj
  have hle : R ≤ Subgroup.zpowers u := by
    intro x hx
    rcases hsub x hx with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers u
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hu2] at this
  omega

end Normalizing


section Normalizing2


end Normalizing2


end CFSG.ClassicalInvolution.Hat2A7T
