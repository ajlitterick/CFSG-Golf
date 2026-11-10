module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.Defs

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {α : Type} [Fintype α] [DecidableEq α]


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
