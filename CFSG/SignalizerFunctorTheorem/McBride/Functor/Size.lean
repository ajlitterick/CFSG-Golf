module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ θ' : G → Subgroup G}

open scoped Classical in
private theorem size_eq_sum [Fintype G] (A : Subgroup G) (θ : G → Subgroup G) :
    size A θ = ∑ a : G, if a ∈ A ∧ a ≠ 1 then Nat.card (θ a) else 0 := by
  unfold size
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases ha : a ∈ A <;> by_cases ha1 : a ≠ 1 <;> simp [ha, ha1]


theorem size_lt_size [Finite G] (h : ∀ a ∈ A, a ≠ 1 → θ' a ≤ θ a)
    (hne : ∃ a ∈ A, a ≠ 1 ∧ θ' a ≠ θ a) : size A θ' < size A θ := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨a₀, ha₀, ha₀1, hne⟩ := hne
  rw [size_eq_sum, size_eq_sum]
  refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ _, ?_⟩
  · split_ifs with hc
    · exact Subgroup.card_le_of_le (h a hc.1 hc.2)
    · exact le_rfl
  · have hc : a₀ ∈ A ∧ a₀ ≠ 1 := ⟨ha₀, ha₀1⟩
    split_ifs
    refine lt_of_le_of_ne (Subgroup.card_le_of_le (h a₀ ha₀ ha₀1)) fun heq => hne ?_
    exact Subgroup.eq_of_le_of_card_ge (h a₀ ha₀ ha₀1) heq.ge


end CFSG.SignalizerFunctorTheorem.McBride
