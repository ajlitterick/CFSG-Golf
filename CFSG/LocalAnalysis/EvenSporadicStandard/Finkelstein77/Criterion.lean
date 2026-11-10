module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def innAut (Y : Type*) [Group Y] : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range


theorem eq_or_eq_top_of_index_dvd_two {Γ : Type*} [Group Γ] {H : Subgroup Γ} (hH : H.index ∣ 2)
    {M : Subgroup Γ} (hM : H ≤ M) : M = H ∨ M = ⊤ := by
  have h2 : M.index ∣ 2 := (Subgroup.index_dvd_of_le hM).trans hH
  have hmul : H.relIndex M * M.index = H.index := Subgroup.relIndex_mul_index hM
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · refine Or.inl (le_antisymm ?_ hM)
    rw [h] at hmul
    have h3 : H.relIndex M * 2 ∣ 1 * 2 := by
      rw [hmul, one_mul]
      exact hH
    have h4 : H.relIndex M ∣ 1 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
    exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp h4)


end CFSG.EvenSporadicStandard.Finkelstein77
