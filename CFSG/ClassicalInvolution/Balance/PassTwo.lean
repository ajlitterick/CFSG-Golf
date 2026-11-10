module

public import CFSG.ClassicalInvolution.Balance.PassTwoStep
public import CFSG.ClassicalInvolution.Balance.OddCentralizerFreeLayer

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic

section Hypotheses

variable {G : Type} [Group G] [Finite G]

theorem componentClassificationOddCore_eq_bot_of_simple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    componentClassificationOddCore G = ⊥ := by
  rcases (inferInstance : (componentClassificationOddCore G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card G) := by
      have := OddCore.odd_card G
      rw [h] at this
      simpa using this
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr hsolv a b)

omit [Finite G] in
theorem not_subset_center_of_ne_one [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : x ≠ 1) : ¬ ({x} : Set G) ⊆ Subgroup.center G := by
  intro hsub
  have hcenter : Subgroup.center G = ⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ Subgroup.center G := by rw [h]; trivial
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  have := hsub (Set.mem_singleton x)
  rw [SetLike.mem_coe, hcenter, Subgroup.mem_bot] at this
  exact hx this

end Hypotheses

section Chain


end Chain

end CFSG.ClassicalInvolution.Balance
