module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisISupport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitDihedralExtension
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open


variable {L : Type} [Group L] [Finite L]

theorem exists_orderOf_eq_two_of_isPGroup {H : Subgroup L} (hH : IsPGroup 2 H) (hne : H ≠ ⊥) :
    ∃ s ∈ H, orderOf s = 2 := by
  obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hH ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 2 ∣ orderOf p := by
    have h1 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hp1'
    · rw [hj]
      exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  exact ⟨p ^ (orderOf p / 2), H.pow_mem hp _, orderOf_pow_orderOf_div (orderOf_pos p).ne' hdvd⟩


end CFSG.ComponentClassification.AschbacherToolkit
