module

public import CFSG.Monster.B.TwoA.Base.Flags

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open Module

open scoped IsMulCommutative

section Lin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_linearEquiv_fix_pointwise {W T T' : Submodule K V} (hT : W ≤ T) (hT' : W ≤ T')
    (h : finrank K T = finrank K T') :
    ∃ e : V ≃ₗ[K] V, (∀ x ∈ W, e x = x) ∧ T.map (e : V →ₗ[K] V) = T' := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hsup : ∀ {S : Submodule K V}, W ≤ S → W ⊔ C ⊓ S = S := fun hS => by
    rw [← sup_inf_assoc_of_le C hS, hC.sup_eq_top, top_inf_eq]
  have hdim : ∀ {S : Submodule K V}, W ≤ S → finrank K ↥(C ⊓ S) + finrank K W = finrank K S := by
    intro S hS
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (C ⊓ S)
    have h2 : W ⊓ (C ⊓ S) = ⊥ := eq_bot_iff.2 fun x hx =>
      hC.disjoint.le_bot ⟨hx.1, hx.2.1⟩
    rw [hsup hS, h2, finrank_bot] at h1
    omega
  let S₁ : Submodule K C := (C ⊓ T).comap C.subtype
  let S₂ : Submodule K C := (C ⊓ T').comap C.subtype
  have hS : finrank K S₁ = finrank K S₂ := by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ T ≤ C)).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ T' ≤ C)).finrank_eq]
    have h1 := hdim hT
    have h2 := hdim hT'
    omega
  obtain ⟨f, hf⟩ := exists_linearEquiv_map_eq hS
  let e : V ≃ₗ[K] V := (Submodule.prodEquivOfIsCompl W C hC).symm.trans
    (((LinearEquiv.refl K W).prodCongr f).trans (Submodule.prodEquivOfIsCompl W C hC))
  have heW : ∀ x : W, e x = x := by
    intro x
    change Submodule.prodEquivOfIsCompl W C hC
      (((LinearEquiv.refl K W).prodCongr f) ((Submodule.prodEquivOfIsCompl W C hC).symm x)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, add_zero]
    rfl
  have heC : ∀ x : C, e x = f x := by
    intro x
    change Submodule.prodEquivOfIsCompl W C hC
      (((LinearEquiv.refl K W).prodCongr f) ((Submodule.prodEquivOfIsCompl W C hC).symm x)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, zero_add]
  have hW : W.map (e : V →ₗ[K] V) = W := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change e (⟨x, hx⟩ : W) ∈ W
      rw [heW]
      exact hx
    · intro x hx
      exact ⟨x, hx, heW ⟨x, hx⟩⟩
  have hCT : (C ⊓ T).map (e : V →ₗ[K] V) = C ⊓ T' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : f ⟨x, hx.1⟩ ∈ S₂ := by
        rw [← hf]
        exact ⟨⟨x, hx.1⟩, hx, rfl⟩
      change e (⟨x, hx.1⟩ : C) ∈ C ⊓ T'
      rw [heC]
      exact h1
    · intro y hy
      have h1 : (⟨y, hy.1⟩ : C) ∈ S₁.map (f : C →ₗ[K] C) := by
        rw [hf]
        exact hy
      obtain ⟨s, hs, hsy⟩ := h1
      refine ⟨s, hs, ?_⟩
      change e s = y
      rw [heC]
      exact congrArg Subtype.val hsy
  refine ⟨e, fun x hx => heW ⟨x, hx⟩, ?_⟩
  rw [← hsup hT, Submodule.map_sup, hW, hCT, hsup hT']

omit [FiniteDimensional K V] in
theorem map_eq_of_le_fix {W U : Submodule K V} {e : V ≃ₗ[K] V} (he : ∀ x ∈ W, e x = x)
    (hU : U ≤ W) : U.map (e : V →ₗ[K] V) = U := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change e x ∈ U
    rw [he x (hU hx)]
    exact hx
  · intro x hx
    exact ⟨x, hx, he x (hU hx)⟩

theorem exists_linearEquiv_map_flag (I : Finset ℕ) (V₁ V₂ : ℕ → Submodule K V)
    (h₁ : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → V₁ i ≤ V₁ j) (h₂ : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → V₂ i ≤ V₂ j)
    (hd : ∀ i ∈ I, finrank K (V₁ i) = finrank K (V₂ i)) :
    ∃ e : V ≃ₗ[K] V, ∀ i ∈ I, (V₁ i).map (e : V →ₗ[K] V) = V₂ i := by
  induction I using Finset.induction_on_max with
  | empty => exact ⟨LinearEquiv.refl K V, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s has ih =>
    obtain ⟨e₀, he₀⟩ := ih (fun i hi j hj hij => h₁ i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj) hij) (fun i hi j hj hij => h₂ i (Finset.mem_insert_of_mem hi)
      j (Finset.mem_insert_of_mem hj) hij) (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have ha := Finset.mem_insert_self a s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · obtain ⟨e, he⟩ := exists_linearEquiv_map_eq ((LinearEquiv.finrank_map_eq e₀ (V₁ a)).trans
        (hd a ha))
      refine ⟨e₀.trans e, fun i hi => ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      swap
      · exact absurd hi (Finset.notMem_empty i)
      rw [LinearEquiv.coe_trans, Submodule.map_comp, he]
    ·
      set b := s.max' hs
      have hb : b ∈ s := s.max'_mem hs
      have hba : b ≤ a := (has b hb).le
      have hW : V₂ b ≤ (V₁ a).map (e₀ : V →ₗ[K] V) := by
        rw [← he₀ b hb]
        exact Submodule.map_mono (h₁ b (Finset.mem_insert_of_mem hb) a ha hba)
      obtain ⟨e₁, he₁, he₁a⟩ := exists_linearEquiv_fix_pointwise hW
        (h₂ b (Finset.mem_insert_of_mem hb) a ha hba)
        ((LinearEquiv.finrank_map_eq e₀ (V₁ a)).trans (hd a ha))
      refine ⟨e₀.trans e₁, fun i hi => ?_⟩
      rw [LinearEquiv.coe_trans, Submodule.map_comp]
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact he₁a
      · rw [he₀ i hi]
        exact map_eq_of_le_fix he₁ (h₂ i (Finset.mem_insert_of_mem hi) b
          (Finset.mem_insert_of_mem hb) (s.le_max' i hi))

omit [FiniteDimensional K V] in
theorem finrank_sup_span_singleton_of_not_mem {U : Submodule K V} [FiniteDimensional K U]
    {x : V} (hx : x ∉ U) : finrank K ↥(U ⊔ K ∙ x) = finrank K U + 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ U.zero_mem)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ x)
  have h2 : U ⊓ (K ∙ x) = ⊥ := ((Submodule.disjoint_span_singleton' hx0).2 hx).eq_bot
  rw [h2, finrank_bot, finrank_span_singleton hx0] at h1
  omega

theorem exists_submodule_between {W T : Submodule K V} (h : W ≤ T) {k : ℕ}
    (hk1 : finrank K W ≤ k) (hk2 : k ≤ finrank K T) : ∃ U, W ≤ U ∧ U ≤ T ∧ finrank K U = k := by
  induction k, hk1 using Nat.le_induction with
  | base => exact ⟨W, le_rfl, h, rfl⟩
  | succ k hk ih =>
    obtain ⟨U, hWU, hUT, hU⟩ := ih (by omega)
    have hlt : U < T := lt_of_le_of_ne hUT fun e => by
      rw [e] at hU
      omega
    obtain ⟨x, hxT, hxU⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨U ⊔ K ∙ x, hWU.trans le_sup_left, sup_le hUT ((Submodule.span_singleton_le_iff_mem
      _ _).2 hxT), ?_⟩
    rw [finrank_sup_span_singleton_of_not_mem hxU, hU]


end Lin

section Corr

variable {G : Type*} [Group G] (E : Subgroup G) [CFSG.IsElementaryAbelian 2 E]


variable {E}


theorem subOf_le_subOf_iff {F F' : Subgroup G} (hF : F ≤ E) :
    subOf E F ≤ subOf E F' ↔ F ≤ F' :=
  ⟨fun h g hg => h (x := Additive.ofMul ⟨g, hF hg⟩) hg, fun h _ hx => h hx⟩


end Corr

end CFSG.Monster.B.TwoA
