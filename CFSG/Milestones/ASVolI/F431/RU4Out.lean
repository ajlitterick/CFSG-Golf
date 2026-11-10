module

public import CFSG.Milestones.ASVolI.F431.RA35Out
public import CFSG.Milestones.ASVolI.F431.RU42
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF4r_ringEquiv_eq_bar {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (τ : K ≃+* K) (hτ : τ ≠ 1) : τ = barEquiv h := by
  have hcard : Nat.card K = 2 ^ 2 := by rw [h.card]
  obtain ⟨σ, hσ, hord, htop, -, -, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 2 2
      Nat.prime_two (by norm_num) K hcard
  have hbar : barEquiv h = σ := by
    ext c
    rw [barEquiv_apply, h.bar_apply, hσ]
    norm_num
  rw [hbar]
  have hτσ : τ ∈ Subgroup.zpowers σ := by rw [← htop]; exact Subgroup.mem_top τ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτσ
  rw [← zpow_mod_orderOf, hord] at hτ ⊢
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [Nat.cast_ofNat, hk, zpow_zero] at hτ
    exact absurd rfl hτ
  · rw [Nat.cast_ofNat, hk, zpow_one]

section U4Out


end U4Out

end CFSG.ASVolI
