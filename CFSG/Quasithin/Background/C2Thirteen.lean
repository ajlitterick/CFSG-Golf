module

public import CFSG.Quasithin.Background.C2Twelve

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H R M L V T : Subgroup G}

@[expose] def ASC213Step (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V : Subgroup G, HypC28 H R M L V → oTwoFstarIn H ≤ M → L ∈ cComp H

namespace C2Thirteen

omit [Finite G] in
theorem conjByElt_injective (g : G) : Function.Injective (conjByElt g) :=
  Subgroup.map_injective (MulAut.conj g).injective

omit [Finite G] in
theorem conjByElt_sup (g : G) (A B : Subgroup G) :
    conjByElt g (A ⊔ B) = conjByElt g A ⊔ conjByElt g B :=
  Subgroup.map_sup _ _ _

omit [Finite G] in
theorem conjByElt_sup_pair {g : G} {L L₂ : Subgroup G} (hne : L₂ ≠ L)
    (h₁ : conjByElt g L = L ∨ conjByElt g L = L₂)
    (h₂ : conjByElt g L₂ = L ∨ conjByElt g L₂ = L₂) :
    conjByElt g (L ⊔ L₂) = L ⊔ L₂ := by
  rw [conjByElt_sup]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact absurd (conjByElt_injective g (h₂.trans h₁.symm)) hne
  · rw [h₁, h₂]
  · rw [h₁, h₂, sup_comm]
  · exact absurd (conjByElt_injective g (h₁.trans h₂.symm)).symm hne

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]


end Abstract


end C2Thirteen

theorem c2_13 (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (hStep : ASC213Step G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M)
    (hRT : R ≤ T) (hF : oTwoFstarIn H ≤ M) :
    H = M ∨ (conjClosure L M = L ∧ L ∈ cComp H ∧
      M = H ⊓ Subgroup.normalizer (conjClosure L M : Set G) ∧ M.relIndex H = 2) := by
  by_cases hMH : H = M
  · exact Or.inl hMH
  right
  have hL : L ∈ cComp H := hStep H R M L V h hF
  have h12 := c2_12 hC129 hC111 hC19 hA3 h hT hRT
  have hnn : ¬ H ≤ Subgroup.normalizer (conjClosure L M : Set G) := fun hHn =>
    hMH ((inf_eq_left.mpr hHn).symm.trans h12)
  obtain ⟨T', hT', hTT'⟩ := B6.exists_isSylowTwoOf_ge hT.2.1 (hT.1.trans h.le_H)
  obtain ⟨hconj, hcase⟩ := hA3 H T' L h.sqtk hT' hL
  rcases hcase with hall | ⟨t, htT', htn, hset, -, -, -⟩
  ·
    exfalso
    have hHL : ∀ g ∈ H, conjByElt g L = L := by
      intro g hg
      have hmem : conjByElt g L ∈ conjSubgroupsBy H L := ⟨g, hg, rfl⟩
      rw [hconj] at hmem
      obtain ⟨t, ht, hteq⟩ := hmem
      rw [show conjByElt g L = conjByElt t L from hteq]
      exact C2Eleven.mem_normalizer_iff_conjByElt.mp (hall t ht)
    have hM0L : conjClosure L M = L := by
      refine le_antisymm (conjClosure_le fun m hm z hz => ?_) (le_conjClosure L M)
      have := C2Eleven.conj_mem_conjByElt (g := m) hz
      rwa [hHL m (h.le_H hm)] at this
    apply hnn
    rw [hM0L]
    exact fun g hg => C2Eleven.mem_normalizer_iff_conjByElt.mpr (hHL g hg)
  ·
    have hne : conjByElt t L ≠ L := fun heq =>
      htn (C2Eleven.mem_normalizer_iff_conjByElt.mpr heq)
    have htH : t ∈ H := hT'.1 htT'
    have hHset : ∀ g ∈ H, conjByElt g L = L ∨ conjByElt g L = conjByElt t L := by
      intro g hg
      have hmem : conjByElt g L ∈ conjSubgroupsBy H L := ⟨g, hg, rfl⟩
      rw [hconj, hset] at hmem
      exact hmem
    have hHset₂ : ∀ g ∈ H, conjByElt g (conjByElt t L) = L ∨
        conjByElt g (conjByElt t L) = conjByElt t L := by
      intro g hg
      rw [← C2Eleven.conjByElt_mul]
      exact hHset (g * t) (H.mul_mem hg htH)
    have hpair : ∀ g ∈ H, conjByElt g (L ⊔ conjByElt t L) = L ⊔ conjByElt t L := fun g hg =>
      C2Thirteen.conjByElt_sup_pair hne (hHset g hg) (hHset₂ g hg)
    obtain ⟨-, hM0, -⟩ := c2_9_one hA3 h hT
    have hM0L : conjClosure L M = L := by
      rcases hM0 with hM0 | ⟨L₂, hL₂T, hL₂ne, hM0eq, -⟩
      · exact hM0
      · exfalso
        obtain ⟨t', ht', hteq⟩ := hL₂T
        have h₂ : L₂ = conjByElt t L := by
          rcases hHset t' (h.le_H (hT.1 ht')) with h₃ | h₃
          · exact absurd (hteq.trans h₃) hL₂ne
          · exact hteq.trans h₃
        apply hnn
        rw [hM0eq, h₂]
        exact fun g hg => C2Eleven.mem_normalizer_iff_conjByElt.mpr (hpair g hg)
    refine ⟨hM0L, hL, h12.symm, ?_⟩
    have hMeq : M = H ⊓ Subgroup.normalizer (L : Set G) := by
      have := h12.symm
      rwa [hM0L] at this
    have hmemM : ∀ g ∈ H, g ∈ M ↔ conjByElt g L = L := by
      intro g hg
      rw [hMeq, Subgroup.mem_inf, C2Eleven.mem_normalizer_iff_conjByElt]
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    show (M.subgroupOf H).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htH⟩, fun b => ?_⟩
    have hb := b.2
    have h1 : b * ⟨t, htH⟩ ∈ M.subgroupOf H ↔ conjByElt (b : G) (conjByElt t L) = L := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmemM _ (H.mul_mem hb htH),
        C2Eleven.conjByElt_mul]
    have h2 : b ∈ M.subgroupOf H ↔ conjByElt (b : G) L = L := by
      rw [Subgroup.mem_subgroupOf, hmemM _ hb]
    rw [h1, h2]
    rcases hHset b hb with h3 | h3
    · have h4 : ¬ conjByElt (b : G) (conjByElt t L) = L := fun h4 =>
        hne (C2Thirteen.conjByElt_injective (b : G) (h4.trans h3.symm))
      exact Or.inr ⟨h3, h4⟩
    · have h4 : conjByElt (b : G) (conjByElt t L) = L := by
        rcases hHset₂ b hb with h5 | h5
        · exact h5
        · exact absurd (C2Thirteen.conjByElt_injective (b : G) (h3.trans h5.symm)) hne.symm
      have h5 : ¬ conjByElt (b : G) L = L := fun h5 => hne (h3.symm.trans h5)
      exact Or.inl ⟨h4, h5⟩


end CFSG.Quasithin
