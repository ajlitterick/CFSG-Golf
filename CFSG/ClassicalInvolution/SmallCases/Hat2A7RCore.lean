module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RFusion

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.AscFusion
open scoped commutatorElement


section Reduction

variable {F : Type} [Group F] [Finite F]

theorem four_le_orderOf_of_not_mem {J K : Subgroup F} {t v : F} (hJ : IsClassical2A7 ⊤ J t)
    (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (htK : t ∈ Subgroup.normalizer (K : Set F)) (hvK : v ∉ Subgroup.normalizer (K : Set F)) :
    4 ≤ orderOf v := by
  obtain ⟨n, hn⟩ := hv2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exfalso
    apply hvK
    interval_cases n
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      rw [hn]
      exact Subgroup.one_mem _
    · have hvt : v = t := hJ.eq_of_orderOf_eq_two hvJ (by rw [hn]; norm_num)
      rw [hvt]
      exact htK
  · rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge


end Reduction

end CFSG.ClassicalInvolution.Hat2A7R
