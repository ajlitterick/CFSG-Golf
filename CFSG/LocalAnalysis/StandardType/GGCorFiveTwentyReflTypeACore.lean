module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

section RankOne

variable {M : Type*} [Group M]

theorem pseudoRefl_rank_one (hp : p.Prime) {A : Subgroup M} [Finite A]
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {β : M} (hN : ∀ a ∈ A, β * a * β⁻¹ ∈ A)
    (hfix : Nat.card {a : A // β * (a : M) * β⁻¹ = a} * p = Nat.card A) {a₁ a₂ : M}
    (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A) :
    β * a₁ * β⁻¹ = a₁ ∨ ∃ e : ℕ, β * (a₁ ^ e * a₂⁻¹) * β⁻¹ = a₁ ^ e * a₂⁻¹ := by
  have := Fact.mk hp
  let δ : A →* A :=
    { toFun := fun a => ⟨β * a * β⁻¹ * (a : M)⁻¹, A.mul_mem (hN _ a.2) (A.inv_mem a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hc := hAc _ (A.mul_mem (hN _ b.2) (A.inv_mem b.2)) _ (A.inv_mem a.2)
        simp only [Subgroup.coe_mul]
        calc β * ((a : M) * b) * β⁻¹ * ((a : M) * b)⁻¹
            = β * a * β⁻¹ * (β * b * β⁻¹ * (b : M)⁻¹ * (a : M)⁻¹) := by group
          _ = β * a * β⁻¹ * ((a : M)⁻¹ * (β * b * β⁻¹ * (b : M)⁻¹)) := by rw [hc]
          _ = β * a * β⁻¹ * (a : M)⁻¹ * (β * b * β⁻¹ * (b : M)⁻¹) := by group) }
  have hδ1 : ∀ a : A, δ a = 1 ↔ β * (a : M) * β⁻¹ = a := by
    intro a
    rw [← Subtype.coe_inj, Subgroup.coe_one]
    exact mul_inv_eq_one
  have hker : Nat.card δ.ker = Nat.card {a : A // β * (a : M) * β⁻¹ = a} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [MonoidHom.mem_ker, hδ1])
  have hrange : Nat.card δ.range = p := by
    have h1 := δ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, ← hfix] at h1
    have hpos : 0 < Nat.card {a : A // β * (a : M) * β⁻¹ = a} := by
      rw [← hker]
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  by_cases ha₁ : δ ⟨a₁, h₁⟩ = 1
  · exact Or.inl ((hδ1 _).mp ha₁)
  right
  have hpow : δ ⟨a₁, h₁⟩ ^ p = 1 := by
    have h1 := pow_card_eq_one' (G := δ.range) (x := ⟨δ ⟨a₁, h₁⟩, ⟨_, rfl⟩⟩)
    rw [hrange] at h1
    simpa using congrArg Subtype.val h1
  have hz : Subgroup.zpowers (δ ⟨a₁, h₁⟩) = δ.range := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := δ.range)).mpr ⟨_, rfl⟩)
    rw [Nat.card_zpowers, orderOf_eq_prime hpow ha₁, hrange]
  have h2 : δ ⟨a₂, h₂⟩ ∈ Submonoid.powers (δ ⟨a₁, h₁⟩) :=
    mem_powers_iff_mem_zpowers.mpr (by rw [hz]; exact ⟨_, rfl⟩)
  obtain ⟨e, he⟩ := h2
  have he' : δ ⟨a₁, h₁⟩ ^ e = δ ⟨a₂, h₂⟩ := he
  refine ⟨e, ?_⟩
  have h3 : δ (⟨a₁, h₁⟩ ^ e * (⟨a₂, h₂⟩ : A)⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, he', mul_inv_cancel]
  simpa using (hδ1 _).mp h3

end RankOne


section NormalForm

variable [Finite K] (hd : 0 < d) (hpd : Nat.Coprime p d)
  {X : Subgroup (MulAut (projectiveSL d K))} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)


include hXc in
theorem conjMat_pow_apply {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc) (e : ℕ) (k : Fin d) :
    conjMat A₀ (g ^ e) k k = conjMat A₀ g k k ^ e := by
  have h := (conjMat_diag hg.1 (hdiag g hg)).1
  calc conjMat A₀ (g ^ e) k k = (conjMat A₀ g ^ e) k k := by rw [conjMat_pow]
    _ = (diagonal (fun i => conjMat A₀ g i i) ^ e) k k := by rw [← h]
    _ = conjMat A₀ g k k ^ e := by rw [diagonal_pow, diagonal_apply_eq, Pi.pow_apply]


include hXc in
theorem permConj_conj_slLift [CharP K 2] {A₀ : GL (Fin d) K}
    (hdiag : ∀ g ∈ slLift hd hpd X hXc, ∀ i j, i ≠ j → conjMat A₀ g i j = 0)
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ g ∈ slLift hd hpd X hXc, conjMat A₀ g = diagonal t)
    (τ : Equiv.Perm (Fin d)) {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ slLift hd hpd X hXc) :
    permConj A₀ τ * g * (permConj A₀ τ)⁻¹ ∈ slLift hd hpd X hXc ∧
      ∀ l, conjMat A₀ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹) l l = conjMat A₀ g (τ l) (τ l) := by
  obtain ⟨t, ht⟩ : ∃ t : Fin d → K, t = fun l => conjMat A₀ g l l := ⟨_, rfl⟩
  have hgd := conjMat_diag hg.1 (hdiag g hg)
  have hgt : conjMat A₀ g = diagonal t := ht ▸ hgd.1
  have hMN : conjMat A₀ (permConj A₀ τ) * conjMat A₀ (permConj A₀ τ)⁻¹ = 1 := by
    rw [← conjMat_mul, mul_inv_cancel, conjMat_one]
  have hc : conjMat A₀ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹) = diagonal (t ∘ τ) := by
    rw [conjMat_mul, conjMat_mul, hgt, conjMat_permConj, permMatrix_mul_diagonal,
      Matrix.mul_assoc, ← conjMat_permConj A₀ τ, hMN, Matrix.mul_one]
  obtain ⟨g'', hg'', hg''t⟩ := hfull (t ∘ τ) (fun l => by rw [ht]; exact hgd.2.1 (τ l))
    (by simp only [Function.comp_apply]; rw [Equiv.prod_comp τ t, ht]; exact hgd.2.2)
  have heq : permConj A₀ τ * g * (permConj A₀ τ)⁻¹ = g'' :=
    conjMat_injective (A := A₀) (hc.trans hg''t.symm)
  refine ⟨heq ▸ hg'', fun l => ?_⟩
  rw [hc, hgt, diagonal_apply_eq, diagonal_apply_eq]
  rfl

end NormalForm

end CFSG.StandardType.TypeA

end
