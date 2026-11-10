module

public import CFSG.ClassicalInvolution.Generic.StepLayer
public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Member

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification
open scoped MatrixGroups

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]


end Basic

section Dichotomy

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]


end Dichotomy

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem inf_oddCoreIn_le {K Y : Subgroup G} (hKY : K ≤ Y) : K ⊓ oddCoreIn Y ≤ oddCoreIn K := by
  refine le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : g * x * g⁻¹ ∈ K ↔ x ∈ K := by
      constructor
      · intro h
        have := K.mul_mem (K.mul_mem (K.inv_mem hg) h) hg
        simpa [mul_assoc] using this
      · intro h
        exact K.mul_mem (K.mul_mem hg h) (K.inv_mem hg)
    have h2 : g * x * g⁻¹ ∈ oddCoreIn Y ↔ x ∈ oddCoreIn Y := by
      constructor
      · intro h
        have := conj_mem_oddCoreIn (X := Y) (Y.inv_mem (hKY hg)) h
        simpa [mul_assoc] using this
      · intro h
        exact conj_mem_oddCoreIn (hKY hg) h
    simp only [Subgroup.mem_inf, h1, h2]
  · exact (odd_card_oddCoreIn Y).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)


end OddCore

end CFSG.ClassicalInvolution.Balance
