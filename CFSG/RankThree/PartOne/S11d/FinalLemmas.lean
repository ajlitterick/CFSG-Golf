module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped Pointwise

theorem exists_isSylowOf_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ T : Subgroup G, ABGLocalTools.IsSylowOf p T K ∧ Q ≤ T := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hS hx, rfl⟩

theorem exists_conj_mem_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K T : Subgroup G} (hT : ABGLocalTools.IsSylowOf p T K) {g : G} (hg : g ∈ K)
    (hgp : ∃ k : ℕ, orderOf g = p ^ k) : ∃ h ∈ K, h * g * h⁻¹ ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨k, hk⟩ := hgp
  have hZ : IsPGroup p (zpowers (⟨g, hg⟩ : K)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk])
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨g, hg⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩


end CFSG.RankThree.PartOne
