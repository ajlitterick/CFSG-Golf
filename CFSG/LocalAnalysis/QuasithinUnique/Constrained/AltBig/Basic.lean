module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.Defs

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {α : Type} [Fintype α] [DecidableEq α]


theorem perfect_fix_pairs (p : FpfInv α) {E : Subgroup (Perm α)} (hE : ⁅E, E⁆ = E) {W : Set α}
    (h : ∀ e ∈ E, ∀ x ∈ W, e x = x ∨ e x = p.μ x) (hW : ∀ x ∈ W, p.μ x ∈ W) :
    ∀ e ∈ E, ∀ x ∈ W, e x = x := by
  have hinv : ∀ (σ : Perm α) (z : α), σ (σ⁻¹ z) = z := fun σ z => by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hA : ∀ e ∈ E, ∀ y ∈ W,
      (e y = y → e (p.μ y) = p.μ y) ∧ (e y = p.μ y → e (p.μ y) = y) := by
    intro e he y hy
    have h' := h e he (p.μ y) (hW y hy)
    rw [p.inv y] at h'
    constructor
    · intro hey
      rcases h' with h1 | h1
      · exact h1
      · exfalso
        apply p.fpf y
        apply e.injective
        rw [h1, hey]
    · intro hey
      rcases h' with h1 | h1
      · exfalso
        apply p.fpf y
        apply e.injective
        rw [h1, hey]
      · exact h1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, ∀ y ∈ W, a (b y) = b (a y) := by
    intro a ha b hb y hy
    obtain ⟨hA1, hA2⟩ := hA a ha y hy
    obtain ⟨hB1, hB2⟩ := hA b hb y hy
    rcases h a ha y hy with ha1 | ha1 <;> rcases h b hb y hy with hb1 | hb1
    · rw [hb1, ha1, hb1]
    · rw [hb1, ha1, hA1 ha1, hb1]
    · rw [hb1, ha1, hB1 hb1]
    · rw [hb1, ha1, hA2 ha1, hB2 hb1]
  have hfix : ∀ g ∈ E, ∀ k ∈ E, ⁅g, k⁆ ∈ fixOn W := by
    intro g hg k hk
    rw [mem_fixOn]
    intro z hz
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    have h1 : g⁻¹ (k⁻¹ z) = k⁻¹ (g⁻¹ z) := hcomm g⁻¹ (E.inv_mem hg) k⁻¹ (E.inv_mem hk) z hz
    rw [h1, hinv k, hinv g]
  have hsub : ⁅E, E⁆ ≤ fixOn W :=
    Subgroup.commutator_le.mpr (fun g hg k hk => hfix g hg k hk)
  rw [hE] at hsub
  intro e he x hx
  exact mem_fixOn.mp (hsub he) x hx


theorem altBigBlockFact {Y : Subgroup (Perm α)} {B : Set α} (hBl : MulAction.IsBlock (↥Y) B)
    {σ : Perm α} (hσ : σ ∈ Y) {b : α} (hb : b ∈ B) (hσb : σ b ∈ B) :
    ∀ z ∈ B, σ z ∈ B := by
  intro z hz
  let g : ↥Y := ⟨σ, hσ⟩
  have hg : ∀ w : α, g • w = σ w := fun _ => rfl
  have hgB : g • B = B := by
    by_contra hne
    have hdis : Disjoint (g • B) ((1 : ↥Y) • B) :=
      hBl (by rw [one_smul]; exact hne)
    rw [one_smul] at hdis
    have h1 : σ b ∈ g • B := Set.mem_smul_set.mpr ⟨b, hb, hg b⟩
    exact Set.disjoint_left.mp hdis h1 hσb
  have hmem : σ z ∈ g • B := Set.mem_smul_set.mpr ⟨z, hz, hg z⟩
  rwa [hgB] at hmem


theorem th3_swap_commute {a b c d : α} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c) (h4 : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all


theorem th3_exists_not_mem {S : Finset α} (h : S.card < Fintype.card α) : ∃ z, z ∉ S := by
  have hlt : S.card < (Finset.univ : Finset α).card := by
    rw [Finset.card_univ]
    exact h
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨z, hz⟩


end CFSG.QuasithinUnique.L246C127.AltBig
