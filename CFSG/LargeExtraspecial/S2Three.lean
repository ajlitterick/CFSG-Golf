module

public import CFSG.LargeExtraspecial.S2SpB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

theorem sp_stab_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    {S : Submodule (ZMod 2) V}
    (hS : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, g a = a → ∀ x ∈ S, g x ∈ S) :
    S = ⊥ ∨ S = (ZMod 2) ∙ a ∨ S = spPerp f ((ZMod 2) ∙ a) ∨ S = ⊤ := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have htop : ∀ x : V, x ∈ spPerp f (⊥ : Submodule (ZMod 2) V) := fun x => by
    rw [spPerp_bot]
    exact Submodule.mem_top
  have hmem : ∀ x : V, x ∈ spPerp f ((ZMod 2) ∙ a) ↔ f a x = 0 := fun x => by
    rw [mem_spPerp]
    constructor
    · exact fun h => h a (Submodule.mem_span_singleton_self a)
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  by_cases h1 : ∃ x ∈ S, f a x = 1
  · obtain ⟨x, hxS, hx⟩ := h1
    right; right; right
    rw [eq_top_iff]
    have hone : ∀ y, f a y = 1 → y ∈ S := by
      intro y hy
      obtain ⟨t, ht, hty⟩ := exists_mem_spRadFix_apply_eq hf (htop a) (htop x) (htop y) hx hy
      rw [← hty]
      exact hS t ht.1.1 ht.1.2.1 x hxS
    intro y _
    rcases zmod2_eq_zero_or_eq_one (f a y) with h0 | h1'
    · have hxy : x + y ∈ S := hone _ (by rw [map_add, hx, h0, add_zero])
      have := S.sub_mem hxy hxS
      rwa [add_sub_cancel_left] at this
    · exact hone y h1'
  push Not at h1
  have hSperp : ∀ x ∈ S, f a x = 0 := fun x hx =>
    (zmod2_eq_zero_or_eq_one _).resolve_right (h1 x hx)
  by_cases h2 : ∃ x ∈ S, x ∉ (ZMod 2) ∙ a
  · obtain ⟨x, hxS, hxa⟩ := h2
    right; right; left
    have hx0 : x ≠ 0 := fun h => hxa (by rw [h]; exact Submodule.zero_mem _)
    have hxne : x ≠ a := fun h => hxa (by rw [h]; exact Submodule.mem_span_singleton_self a)
    have hgood : ∀ y, f a y = 0 → y ∉ (ZMod 2) ∙ a → y ∈ S := by
      intro y hy hya
      have hy0 : y ≠ 0 := fun h => hya (by rw [h]; exact Submodule.zero_mem _)
      have hyne : y ≠ a := fun h => hya (by rw [h]; exact Submodule.mem_span_singleton_self a)
      obtain ⟨g, hg, hga, hgx⟩ := exists_mem_spRadGen_apply_eq_orth hf hnd hF (htop a) (htop x)
        (htop a) (htop y) ha0 hx0 ha0 hy0 (hSperp x hxS) hxne hy hyne
      rw [← hgx]
      exact hS g (spRadGen_le_spFix ⊥ hg).1 hga x hxS
    refine le_antisymm (fun y hy => (hmem y).mpr (hSperp y hy)) fun y hy => ?_
    rw [hmem] at hy
    by_cases hya : y ∈ (ZMod 2) ∙ a
    · rcases mem_span_singleton_iff.mp hya with h0 | h0
      · rw [h0]
        exact S.zero_mem
      · rw [h0] at hy ⊢
        have hax : a + x ∈ S := hgood _ (by rw [map_add, hy, hSperp x hxS, add_zero])
          (fun h => hxa (by
            have := Submodule.sub_mem _ h (Submodule.mem_span_singleton_self a)
            rwa [add_sub_cancel_left] at this))
        have := S.sub_mem hax hxS
        rwa [add_sub_cancel_right] at this
    · exact hgood y hy hya
  · push Not at h2
    by_cases haS : a ∈ S
    · right; left
      exact le_antisymm h2 ((Submodule.span_singleton_le_iff_mem a S).mpr haS)
    · left
      rw [eq_bot_iff]
      intro y hy
      rcases mem_span_singleton_iff.mp (h2 y hy) with h | h
      · exact (Submodule.mem_bot _).mpr h
      · exact absurd (h ▸ hy) haS

theorem sp_finrank_stab_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    {S : Submodule (ZMod 2) V}
    (hS : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, g a = a → ∀ x ∈ S, g x ∈ S) :
    finrank (ZMod 2) S ≤ 1 ∨ finrank (ZMod 2) V ≤ finrank (ZMod 2) S + 1 := by
  rcases sp_stab_invariant hf hnd ha0 hS with rfl | rfl | rfl | rfl
  · left
    rw [finrank_bot]
    omega
  · left
    rw [finrank_span_singleton ha0]
  · right
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton ha0]
    omega
  · right
    rw [finrank_top]
    omega

theorem sp_even_finrank_spPerp (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    ∀ (n : ℕ) (F : Submodule (ZMod 2) V), F ⊓ spPerp f F = ⊥ →
      finrank (ZMod 2) (spPerp f F) = n → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hn
  by_cases hne : spPerp f F = ⊥
  · rw [hne, finrank_bot] at hn
    rw [← hn]
    exact even_iff_two_dvd.mpr (dvd_zero 2)
  obtain ⟨p, hpF, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p₁, hp₁F, hpp₁⟩ := sp_exists_partner hf hnd hF hpF hp0
  have hK := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
  have hKdim := finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  have h := ih (n - 2) (by omega) _ hK (by omega)
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

theorem sp_even_finrank (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    Even (finrank (ZMod 2) V) := by
  have := sp_even_finrank_spPerp hf hnd _ ⊥ (bot_inf_eq _) rfl
  rwa [spPerp_bot, finrank_top] at this

section Dim

variable {M W : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable [AddCommGroup W] [Module (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_map_add_finrank_inf_ker (φ : M →ₗ[ZMod 2] W) (D : Submodule (ZMod 2) M) :
    finrank (ZMod 2) (D.map φ) + finrank (ZMod 2) ↥(D ⊓ LinearMap.ker φ) =
      finrank (ZMod 2) D := by
  have h := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict D)
  rw [LinearMap.range_domRestrict] at h
  have hk : (LinearMap.ker (φ.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker φ := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply,
      Submodule.coe_subtype, Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, hv'⟩
      exact ⟨⟨v, hv⟩, hv', rfl⟩
  rw [← hk, Submodule.finrank_map_subtype_eq]
  exact h


end Dim

section Module

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

@[expose] def IsIndecomposable {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[ZMod 2] M)) : Prop :=
  ∀ A B : Submodule (ZMod 2) M, (∀ g, ∀ v ∈ A, ρ g v ∈ A) → (∀ g, ∀ v ∈ B, ρ g v ∈ B) →
    IsCompl A B → A = ⊥ ∨ B = ⊥

@[expose] noncomputable def spT (hf : f.IsAlt) (a : V) : TauCeti.BilinForm.isometryGroup f :=
  ⟨spTransvection f hf a, spTransvection_mem_isometryGroup hf a⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem spT_apply (hf : f.IsAlt) (a x : V) : (spT hf a : V ≃ₗ[ZMod 2] V) x = x + f x a • a :=
  spTransvection_apply hf a x

omit [FiniteDimensional (ZMod 2) V] in
theorem spT_conj (hf : f.IsAlt) (g : TauCeti.BilinForm.isometryGroup f) (a : V) :
    g * spT hf a * g⁻¹ = spT hf ((g : V ≃ₗ[ZMod 2] V) a) := by
  refine Subtype.ext ?_
  change (g : V ≃ₗ[ZMod 2] V) * spTransvection f hf a * (g : V ≃ₗ[ZMod 2] V)⁻¹ =
    spTransvection f hf ((g : V ≃ₗ[ZMod 2] V) a)
  rw [← spSiegel_zero_one, ← spSiegel_zero_one, spSiegel_conj hf g.2 (map_zero _), map_zero]

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) M] in
theorem rho_spT_sub (hf : f.IsAlt) (g : TauCeti.BilinForm.isometryGroup f) (a : V) (v : M) :
    ρ g (ρ (spT hf a) v - v) =
      ρ (spT hf ((g : V ≃ₗ[ZMod 2] V) a)) (ρ g v) - ρ g v := by
  rw [← spT_conj hf g a, map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply', map_sub]


omit [FiniteDimensional (ZMod 2) M] in
theorem sp_le_closure_spTransvection (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    TauCeti.BilinForm.isometryGroup f ≤ Subgroup.closure (Set.range (spTransvection f hf)) := by
  set T := Subgroup.closure (Set.range (spTransvection f hf)) with hT
  have hTa : ∀ a, spTransvection f hf a ∈ T := fun a => Subgroup.subset_closure ⟨a, rfl⟩
  have hrad : ∀ p : V, p ≠ 0 → spPointRadical f p ≤ T := by
    intro p hp0 t ht
    obtain ⟨u, hpu, c, rfl⟩ := (mem_spPointRadical_iff hf hnd hp0).mp ht
    have h0 : spSiegel f hf p u 0 ∈ T := by
      have e : spSiegel f hf p u 0 =
          spTransvection f hf p * spTransvection f hf u * spTransvection f hf (p + u) := by
        ext x
        have hup : f u p = 0 := by rw [isAlt_symm hf, hpu]
        rw [spSiegel_apply hf hpu, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          spTransvection_apply, spTransvection_apply, spTransvection_apply]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hf.self_eq_zero, hpu, hup, mul_zero, add_zero, zero_mul]
        refine eq_of_one_smul_eq ?_
        match_scalars <;> ring_nf <;> reduce_mod_char
      rw [e]
      exact mul_mem (mul_mem (hTa p) (hTa u)) (hTa (p + u))
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exact h0
    · have e : spSiegel f hf p u 1 = spSiegel f hf p u 0 * spTransvection f hf p := by
        rw [← spSiegel_one_mul_zero_one hf hpu, mul_assoc, spSiegel_zero_one,
          ← spSiegel_zero_one, spSiegel_mul_self hf (map_zero _), mul_one]
      rw [e]
      exact mul_mem h0 (hTa p)
  have hgen := spFix_le_spRadGen hf hnd (finrank (ZMod 2) V / 2) ⊥ (bot_inf_eq _) (by
    rw [spPerp_bot, finrank_top]
    obtain ⟨b, hb⟩ := sp_even_finrank hf hnd
    omega)
  rw [spFix_bot] at hgen
  refine hgen.trans ?_
  rw [spRadGen, Subgroup.closure_le]
  rintro t ⟨p, -, hp0, ht⟩
  exact hrad p hp0 (by rw [← spRadFix_bot]; exact ht)

end Module

end S2

end CFSG.LargeExtraspecial
