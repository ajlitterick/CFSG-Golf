module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup

private theorem factorization_two_card {P : Type*} (hP : Nat.card P = 898128000) :
    (Nat.card P).factorization 2 = 7 := by
  rw [hP, show (898128000 : ℕ) = 2 ^ 7 * 7016625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]


private theorem exists_conj_mem_of_card_two_pow {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 898128000) {S₀ S : Subgroup P} (hS₀ : Nat.card ↥S₀ = 2 ^ 7)
    (hS : Nat.card ↥S = 2 ^ 7) : ∃ g : P, ∀ a ∈ S₀, g * a * g⁻¹ ∈ S := by
  have h2 := factorization_two_card hP
  have hS₀' : Nat.card ↥S₀ = 2 ^ (Nat.card P).factorization 2 := by rw [h2]; exact hS₀
  have hS' : Nat.card ↥S = 2 ^ (Nat.card P).factorization 2 := by rw [h2]; exact hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard S₀ hS₀') (Sylow.ofCard S hS')
  refine ⟨g, fun a ha => ?_⟩
  have hmem : g * a * g⁻¹ ∈ ((g • Sylow.ofCard S₀ hS₀' : Sylow 2 P) : Subgroup P) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨a, ha, by simp [MulAut.smul_def]⟩
  rw [hg] at hmem
  simpa using hmem


theorem noThree_of_normalizer {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 898128000)
    {S₀ : Subgroup P} (hS₀ : Nat.card ↥S₀ = 2 ^ 7)
    (h : ∀ W : Subgroup P, IsPGroup 3 ↥W → S₀ ≤ normalizer (W : Set P) → W = ⊥)
    {Q : Type*} [Group Q] (φ : Q ≃* P) {S : Subgroup Q} (hS : Nat.card ↥S = 2 ^ 7)
    {W : Subgroup Q} (hW : IsPGroup 3 ↥W) (hn : S ≤ normalizer (W : Set Q)) : W = ⊥ := by
  rw [← Subgroup.map_eq_bot_iff_of_injective W (f := φ.toMonoidHom) φ.injective]
  have hS' : Nat.card ↥(S.map φ.toMonoidHom) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective φ.injective, hS]
  have hn' : S.map φ.toMonoidHom ≤ normalizer ((W.map φ.toMonoidHom : Subgroup P) : Set P) :=
    (Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map _)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card_two_pow hP hS₀ hS'
  set W' := W.map φ.toMonoidHom
  have hW'' : IsPGroup 3 ↥(W'.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (hW.map φ.toMonoidHom).map _
  have hbot := h _ hW'' (fun a ha => by
    rw [mem_normalizer_iff]
    intro x
    have hga := (mem_normalizer_iff.1 (hn' (hg a ha)))
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨g * a * g⁻¹ * w * (g * a * g⁻¹)⁻¹, (hga w).1 hw, by group⟩
    · rintro ⟨w, hw, hwx⟩
      refine ⟨(g * a * g⁻¹)⁻¹ * w * (g * a * g⁻¹), ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem (hn' (hg a ha))) w).1 hw
        simp only [inv_inv] at this
        exact this
      · have hx : x = a⁻¹ * (a * x * a⁻¹) * a := by group
        rw [hx, ← hwx]
        group)
  rw [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective] at hbot
  exact hbot

end CFSG.Sporadic.Recognition.McLAS
