module

public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.ASVolI

open scoped Pointwise

section Core

variable {A : Type} [Group A]


theorem burnsideAut_mem_sup_iff {Y X : Subgroup A} (hXY : X ≤ Subgroup.normalizer (Y : Set A))
    {x : A} : x ∈ Y ⊔ X ↔ ∃ y ∈ Y, ∃ z ∈ X, x = y * z := by
  constructor
  · intro hx
    have : x ∈ ((Y ⊔ X : Subgroup A) : Set A) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y X hXY] at this
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 this
    exact ⟨y, hy, z, hz, rfl⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

variable [Finite A]

theorem burnsideAut_disjoint_of_odd {S H : Subgroup A} (hS : IsPGroup 2 S) (hH : Odd (Nat.card H)) :
    Disjoint S H := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hH)


theorem burnsideAut_conj_of_complements {p : ℕ} [Fact p.Prime] {E Z Y : Subgroup A}
    (hZE : Z ≤ Subgroup.normalizer (E : Set A)) (hYE : Y ≤ Subgroup.normalizer (E : Set A))
    (hE : IsPGroup p E) (hZp : ¬ p ∣ Nat.card Z)
    (hEZ : Disjoint E Z) (hEY : Disjoint E Y) (hYZ : E ⊔ Y = E ⊔ Z) :
    ∃ e ∈ E, Y.map (MulAut.conj e).toMonoidHom = Z := by
  set H₀ : Subgroup A := E ⊔ Z with hH₀
  have hEH : E ≤ H₀ := le_sup_left
  have hZH : Z ≤ H₀ := le_sup_right
  have hYH : Y ≤ H₀ := hYZ ▸ le_sup_right
  have hH₀N : H₀ ≤ Subgroup.normalizer (E : Set A) := sup_le Subgroup.le_normalizer hZE
  haveI : (E.subgroupOf H₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).2 hH₀N
  have hmul : ∀ g ∈ H₀, ∃ e ∈ E, ∃ z ∈ Z, e * z = g := by
    intro g hg
    obtain ⟨e, he, z, hz, rfl⟩ := (burnsideAut_mem_sup_iff hZE).1 hg
    exact ⟨e, he, z, hz, rfl⟩
  have hmulY : ∀ g ∈ H₀, ∃ e ∈ E, ∃ y ∈ Y, e * y = g := by
    intro g hg
    have hg' : g ∈ E ⊔ Y := hYZ ▸ hg
    obtain ⟨e, he, y, hy, rfl⟩ := (burnsideAut_mem_sup_iff hYE).1 hg'
    exact ⟨e, he, y, hy, rfl⟩
  have hN : IsPGroup p (E.subgroupOf H₀) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  have hZg : ¬ p ∣ Nat.card (Z.subgroupOf H₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    exact hZp
  have hdisj : ∀ {W : Subgroup A}, Disjoint E W → Disjoint (E.subgroupOf H₀) (W.subgroupOf H₀) := by
    intro W hW
    rw [Subgroup.disjoint_def] at hW ⊢
    intro x hx1 hx2
    have := hW hx1 hx2
    exact Subtype.ext this
  have htop : ∀ {W : Subgroup A}, W ≤ H₀ → (∀ g ∈ H₀, ∃ e ∈ E, ∃ w ∈ W, e * w = g) →
      E.subgroupOf H₀ ⊔ W.subgroupOf H₀ = ⊤ := by
    intro W hW hmulW
    rw [eq_top_iff]
    intro g _
    obtain ⟨e, he, w, hw, hew⟩ := hmulW g.1 g.2
    have h1 : (⟨e, hEH he⟩ : H₀) ∈ E.subgroupOf H₀ := he
    have h2 : (⟨w, hW hw⟩ : H₀) ∈ W.subgroupOf H₀ := hw
    have : g = ⟨e, hEH he⟩ * ⟨w, hW hw⟩ := Subtype.ext hew.symm
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  obtain ⟨n, hn, hnY⟩ := CFSG.GH74.BNPair.exists_conj_of_complements_top (p := p) hN hZg
    (hdisj hEZ) (hdisj hEY) (htop hZH hmul) (htop hYH hmulY)
  refine ⟨(n : A), hn, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : (⟨y, hYH hy⟩ : H₀) ∈ Y.subgroupOf H₀ := hy
    have h2 : n * ⟨y, hYH hy⟩ * n⁻¹ ∈ Z.subgroupOf H₀ := by
      rw [← hnY]
      exact Subgroup.mem_map.2 ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa [MulAut.conj_apply] using h3
  · intro hx
    have h1 : (⟨x, hZH hx⟩ : H₀) ∈ Z.subgroupOf H₀ := hx
    rw [← hnY] at h1
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
    refine ⟨(y : A), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this


end Core

section Borel

@[expose] def burnsideAut_SolvBorel (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, S ≤ Y → Group.IsSolvable ↥Y → Y ≤ Subgroup.normalizer (S : Set X)


end Borel

end CFSG.ASVolI
