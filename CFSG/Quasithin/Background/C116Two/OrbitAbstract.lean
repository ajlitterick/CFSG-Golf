module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.C116Two

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_commute {Y K : Subgroup G} (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) :
    Y ≤ Subgroup.normalizer (K : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : y * x = x * y := hYK y hy x hx
    have h2 : y * x * y⁻¹ = x := by rw [h1]; group
    rwa [h2]
  · intro hk
    have h1 := hYK y hy _ hk
    have h2 : y * (y * x * y⁻¹) = y * x := by rw [h1]; group
    have h3 : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = y⁻¹ * (y * (y * x * y⁻¹)) := by group
        _ = y⁻¹ * (y * x) := by rw [h2]
        _ = x := by group
    rwa [h3] at hk

theorem relIndex_sup_eq_of_le_normalizer' {Y K : Subgroup G} (hY : Y ≤ Subgroup.normalizer (K : Set G)) :
    K.relIndex (Y ⊔ K) = K.relIndex Y := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hY
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hY
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient Y K hY).toEquiv.symm

theorem card_sup_mul_card_inf_of_commute {Y K : Subgroup G}
    (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) :
    Nat.card ↥(Y ⊔ K) * Nat.card ↥(Y ⊓ K) = Nat.card ↥Y * Nat.card ↥K := by
  have h1 := relIndex_sup_eq_of_le_normalizer' (le_normalizer_of_commute hYK)
  have h2 := Subgroup.relIndex_mul_card K (Y ⊔ K)
  have h3 := Subgroup.relIndex_mul_card K Y
  have h4 : K ⊓ (Y ⊔ K) = K := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3]
  ring


end CFSG.Quasithin.C116Two
