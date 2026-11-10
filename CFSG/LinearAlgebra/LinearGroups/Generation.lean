module

public import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

namespace CFSG.LinearGroups

open Matrix

variable {K : Type*} [Field K] {n : ℕ}


theorem special_linear_elementary_generation :
    Subgroup.closure (elementarySet n K) = ⊤ := by
  rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := K)]
  congr 1
  ext A
  constructor
  · rintro ⟨i, j, hij, c, rfl⟩
    exact ⟨⟨i, j, hij, c⟩, rfl⟩
  · rintro ⟨⟨i, j, hij, c⟩, rfl⟩
    exact ⟨i, j, hij, c, rfl⟩

theorem field_scalar_with_nontrivial_square (hK : ∃ s : Finset K, s.card = 4) :
    ∃ l : Kˣ, l ^ 2 ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := hK
  by_contra h
  push Not at h
  have hsub : s ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h2 := congrArg Units.val (h (Units.mk0 a ha))
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h2
      rcases sq_eq_one_iff.mp h2 with rfl | rfl <;> simp
  have h3 : ({0, 1, -1} : Finset K).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (by simp)))
  have := Finset.card_le_card hsub
  omega

theorem exists_finset_card_eq_four {α : Type*} (hα : 4 ≤ Nat.card α) :
    ∃ s : Finset α, s.card = 4 := by
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite α
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hα)
  exact ⟨s, hs⟩

end CFSG.LinearGroups
