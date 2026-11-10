module

public import CFSG.Quasithin.Recognition.F112TitsMain3
public import CFSG.Quasithin.Background.C124L2MP

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Orders

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_card_oTwoQuot_mul_card_pCoreOf (X : Subgroup G) :
    Nat.card ↥X = Nat.card (oTwoQuot ↥X) * Nat.card ↥(pCoreOf 2 X) := by
  have h : Nat.card ↥(pCoreOf 2 X) = Nat.card ↥(CFSG.Open.pCore 2 ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [h]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_perm_fin_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_eq_two_mul_of_perm_three {X S : Subgroup G} (hS : IsSylowTwoOf S X)
    (hX : Nonempty (oTwoQuot ↥X ≃* Equiv.Perm (Fin 3))) :
    Nat.card ↥S = 2 * Nat.card ↥(pCoreOf 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hX
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 X)
  have hX6 : Nat.card ↥X = 2 ^ (a + 1) * 3 := by
    rw [card_eq_card_oTwoQuot_mul_card_pCoreOf, Nat.card_congr e.toEquiv, card_perm_fin_three,
      ha, pow_succ]
    ring
  rw [card_sylow_eq_pow hS.1 hS (by decide) hX6, ha, pow_succ, mul_comm]

theorem le_of_card_le_card_inf {S L : Subgroup G} (h : Nat.card ↥S ≤ Nat.card ↥(S ⊓ L)) :
    S ≤ L := by
  have heq : S ⊓ L = S := Subgroup.eq_of_le_of_card_ge inf_le_left h
  rw [← heq]
  exact inf_le_right

theorem card_inf_of_card_oTwoQuot {S L : Subgroup G} (hS : IsSylowTwoOf (S ⊓ L) L) {j m : ℕ}
    (hm : ¬ 2 ∣ m) (hL : Nat.card (oTwoQuot ↥L) = 2 ^ j * m) :
    Nat.card ↥(S ⊓ L) = 2 ^ j * Nat.card ↥(pCoreOf 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 L)
  have hL' : Nat.card ↥L = 2 ^ (j + a) * m := by
    rw [card_eq_card_oTwoQuot_mul_card_pCoreOf, hL, ha, pow_add]
    ring
  rw [card_sylow_eq_pow hS.1 hS hm hL', ha, pow_add]


end Orders

section Orient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isL2Quot_of_perm_three {X : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hX : Nonempty (oTwoQuot ↥X ≃* Equiv.Perm (Fin 3))) : ¬ IsL2Quot f (oTwoQuot ↥X) := by
  intro h
  obtain ⟨e⟩ := hX
  have h1 := h.card (by omega)
  rw [Nat.card_congr e.toEquiv, card_perm_fin_three] at h1
  have := two_pow_mul_four_pow_sub_one_ge f hf
  omega

omit [Finite G] in
theorem orient_of_isL2Quot_left {L₂ Y L1' L2' : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hY : Nonempty (oTwoQuot ↥Y ≃* Equiv.Perm (Fin 3)))
    (hor : (L1' = L₂ ∧ L2' = Y) ∨ (L1' = Y ∧ L2' = L₂)) (h : IsL2Quot f (oTwoQuot ↥L1')) :
    L1' = L₂ ∧ L2' = Y := by
  rcases hor with h1 | ⟨rfl, -⟩
  · exact h1
  · exact absurd h (not_isL2Quot_of_perm_three hf hY)

omit [Finite G] in
theorem orient_of_isL2Quot_right {L₂ Y L1' L2' : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hY : Nonempty (oTwoQuot ↥Y ≃* Equiv.Perm (Fin 3)))
    (hor : (L1' = L₂ ∧ L2' = Y) ∨ (L1' = Y ∧ L2' = L₂)) (h : IsL2Quot f (oTwoQuot ↥L2')) :
    L1' = Y ∧ L2' = L₂ := by
  rcases hor with ⟨-, rfl⟩ | h1
  · exact absurd h (not_isL2Quot_of_perm_three hf hY)
  · exact h1

omit [Finite G] in
theorem orient_of_perm_five {L₂ Y S L1' L2' : Subgroup G} (hSY : S ≤ Y)
    (hY : Nonempty (oTwoQuot ↥Y ≃* Equiv.Perm (Fin 3)))
    (hor : (L1' = L₂ ∧ L2' = Y) ∨ (L1' = Y ∧ L2' = L₂))
    (h : Nonempty (oTwoQuot ↥(L1' ⊔ S) ≃* Equiv.Perm (Fin 5))) : L1' = L₂ ∧ L2' = Y := by
  rcases hor with h1 | ⟨rfl, -⟩
  · exact h1
  · exfalso
    rw [sup_eq_left.mpr hSY] at h
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := hY
    have h1 := Nat.card_congr e.toEquiv
    rw [Nat.card_congr e'.toEquiv, card_perm_fin_three, card_perm_fin_five] at h1
    omega

end Orient

section AutJ2


end AutJ2

end CFSG.Quasithin.H13
