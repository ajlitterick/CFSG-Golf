module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OrbitsTwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Counting

theorem ncard_mul_eq_of_ne {ε : h.fixedField} (hε : ε ≠ 0) :
    {p : h.fixedField × h.fixedField | p.1 * p.2 = ε}.ncard = 2 ^ f - 1 := by
  have := h.finite
  have hset : {p : h.fixedField × h.fixedField | p.1 * p.2 = ε} =
      (fun b => (b, ε / b)) '' {b | b ≠ 0} := by
    ext ⟨b, d⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
    constructor
    · intro e
      have hb : b ≠ 0 := by
        rintro rfl
        rw [zero_mul] at e
        exact hε e.symm
      exact ⟨b, hb, rfl, by rw [← e]; field_simp⟩
    · rintro ⟨b', hb', rfl, rfl⟩
      field_simp
  rw [hset, Set.ncard_image_of_injective _ (fun x y e => (Prod.mk.inj e).1)]
  have : {b : h.fixedField | b ≠ 0} = Set.univ \ {0} := by
    ext b
    simp
  rw [this, Set.ncard_sdiff (by simp), Set.ncard_univ, Set.ncard_singleton, h.card_fixedField]

theorem ncard_mul_eq_zero :
    {p : h.fixedField × h.fixedField | p.1 * p.2 = 0}.ncard = 2 * 2 ^ f - 1 := by
  have := h.finite
  have hset : {p : h.fixedField × h.fixedField | p.1 * p.2 = 0} =
      {p | p.1 = 0} ∪ {p | p.2 = 0} := by
    ext p
    simp [mul_eq_zero]
  have h1 : ({p : h.fixedField × h.fixedField | p.1 = 0}).ncard = 2 ^ f := by
    rw [show {p : h.fixedField × h.fixedField | p.1 = 0} = (fun d => ((0 : h.fixedField), d)) ''
      Set.univ by ext ⟨b, d⟩; simp [eq_comm],
      Set.ncard_image_of_injective _ (fun x y e => (Prod.mk.inj e).2), Set.ncard_univ,
      h.card_fixedField]
  have h2 : ({p : h.fixedField × h.fixedField | p.2 = 0}).ncard = 2 ^ f := by
    rw [show {p : h.fixedField × h.fixedField | p.2 = 0} = (fun b => (b, (0 : h.fixedField))) ''
      Set.univ by ext ⟨b, d⟩; simp [eq_comm],
      Set.ncard_image_of_injective _ (fun x y e => (Prod.mk.inj e).1), Set.ncard_univ,
      h.card_fixedField]
  have h3 : ({p : h.fixedField × h.fixedField | p.1 = 0} ∩ {p | p.2 = 0}).ncard = 1 := by
    rw [show {p : h.fixedField × h.fixedField | p.1 = 0} ∩ {p | p.2 = 0} = {(0, 0)} by
      ext ⟨b, d⟩; simp, Set.ncard_singleton]
  have := Set.ncard_union_add_ncard_inter {p : h.fixedField × h.fixedField | p.1 = 0}
    {p | p.2 = 0}
  rw [hset]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega


theorem ncard_norm_eq_zero : {c : K | h.normHom c = 0}.ncard = 1 := by
  rw [show {c : K | h.normHom c = 0} = {0} by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hc
      have := congrArg Subtype.val hc
      simp only [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm, ZeroMemClass.coe_zero,
        mul_eq_zero, map_eq_zero, or_self] at this
      exact this
    · rintro rfl
      exact Subtype.ext (by simp [UnitaryFieldData.norm]), Set.ncard_singleton]

@[expose] def miyamotoQEquiv (δ : h.fixedField) :
    {p : h.fixedField × K × h.fixedField // h.normHom p.2.1 + p.1 * p.2.2 = δ} ≃
      Σ c : K, {r : h.fixedField × h.fixedField // r.1 * r.2 = δ - h.normHom c} where
  toFun p := ⟨p.1.2.1, ⟨(p.1.1, p.1.2.2), by have := p.2; simp only; linear_combination this⟩⟩
  invFun s := ⟨(s.2.1.1, s.1, s.2.1.2), by have := s.2.2; simp only; linear_combination this⟩
  left_inv p := rfl
  right_inv s := rfl

theorem ncard_normHom_add_mul_eq (δ : h.fixedField) :
    {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = δ}.ncard =
      (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f * {c : K | h.normHom c = δ}.ncard := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have := Fintype.ofFinite h.fixedField
  rw [← Nat.card_coe_set_eq, Set.coe_ofPred, Nat.card_congr (miyamotoQEquiv h δ), Nat.card_sigma]
  have hfib : ∀ c : K, Nat.card {r : h.fixedField × h.fixedField // r.1 * r.2 = δ - h.normHom c} =
      (2 ^ f - 1) + (if h.normHom c = δ then 2 ^ f else 0) := by
    intro c
    rw [← Set.coe_ofPred, Nat.card_coe_set_eq]
    by_cases hc : h.normHom c = δ
    · rw [hc, sub_self, ncard_mul_eq_zero]
      simp only [↓reduceIte]
      have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    · rw [ncard_mul_eq_of_ne h (sub_ne_zero.2 (Ne.symm hc))]
      simp [hc]
  simp only [hfib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, h.card_eq_sq, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, mul_comm (Finset.card _)]
  congr 2
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext c
  simp

theorem ncard_normHom_add_mul_eq_zero :
    {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = 0}.ncard =
      (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f := by
  rw [ncard_normHom_add_mul_eq, ncard_norm_eq_zero, mul_one]


end Counting

section OrbitsA1

variable [CharP K 2]

theorem ncard_A1_Q_eq (δ : h.fixedField) :
    {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = δ}.ncard =
      {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = δ}.ncard := by
  have hset : {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = δ} =
      (fun p : h.fixedField × K × h.fixedField => miyamotoXGL h 0 p.1 p.2.1 p.2.2) ''
        {p | h.normHom p.2.1 + p.1 * p.2.2 = δ} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hQ⟩
      obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
      refine ⟨(⟨b, hb⟩, c, ⟨d, hd⟩), Subtype.ext ?_, rfl⟩
      rw [miyamotoQA1_miyamotoXGL] at hQ
      simpa [UnitaryFieldData.norm] using hQ
    · rintro ⟨⟨b, c, d⟩, hp, rfl⟩
      refine ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, b.2, d.2⟩, ?_⟩
      rw [miyamotoQA1_miyamotoXGL]
      have := congrArg Subtype.val hp
      simpa [UnitaryFieldData.norm] using this
  rw [hset, Set.ncard_image_of_injective]
  intro p p' e
  obtain ⟨-, e2, e3, e4⟩ := (miyamotoXGL_inj h).1 e
  exact Prod.ext (Subtype.ext e2) (Prod.ext e3 (Subtype.ext e4))

theorem ncard_A1_Q_eq_zero :
    {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0}.ncard = (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f := by
  have := ncard_A1_Q_eq h 0
  simp only [ZeroMemClass.coe_zero] at this
  rw [this, ncard_normHom_add_mul_eq_zero]

theorem ncard_miyamotoA1 : (miyamotoA1 h : Set (GL (Fin 4) K)).ncard = (2 ^ f) ^ 4 := by
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_miyamotoA1]

theorem ncard_orbit_z1_N1 :
    {y | ∃ n ∈ miyamotoN1 h, n⁻¹ * miyamotoZ1 K * n = y}.ncard =
      (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
  have := h.finite
  rw [miyamoto_orbit_z1_N1 h]
  have hset : {x | x ∈ miyamotoA1 h ∧ x ≠ 1 ∧ miyamotoQA1 h x = 0} =
      {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} \ {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  have h1 : (1 : GL (Fin 4) K) ∈ {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} :=
    ⟨one_mem _, by rw [← miyamotoXGL_zero h, miyamotoQA1_miyamotoXGL]; simp⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem h1, ncard_A1_Q_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

theorem ncard_orbit_z1 :
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * miyamotoZ1 K * g = y}.ncard =
      (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
  rw [miyamoto_orbit_z1_I1N1 h, ← miyamoto_orbit_z1_N1 h, ncard_orbit_z1_N1]


theorem ncard_orbit_z2 :
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y}.ncard =
      (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) := by
  have := h.finite
  rw [miyamoto_orbit_z2_I1N1 h]
  have hset : {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x ≠ 0} =
      (miyamotoA1 h : Set (GL (Fin 4) K)) \ {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe]
    tauto
  have hsub : {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} ⊆ (miyamotoA1 h : Set (GL (Fin 4) K)) :=
    fun x hx => hx.1
  rw [hset, Set.ncard_sdiff hsub (Set.toFinite _), ncard_miyamotoA1, ncard_A1_Q_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  have e : (k + 1) ^ 4 = (k + 1) ^ 2 * k + (k + 1) + k * (k + 1) * ((k + 1) ^ 2 + 1) := by ring
  omega

end OrbitsA1

section OrbitsA2


end OrbitsA2

end CFSG.LocalAnalysis.EvenBN.U4
