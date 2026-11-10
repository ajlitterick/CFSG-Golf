module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoKGroup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped Pointwise

section Elem

variable {A B : Type*} [Group A] [Group B] {p : ℕ}

theorem ggIsElemAbelian_map {E : Subgroup A} (hE : IsElemAbelian p E) (f : A →* B) :
    IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem ggIsElemAbelian_subgroupOf {E : Subgroup A} (hE : IsElemAbelian p E) (W : Subgroup A) :
    IsElemAbelian p (E.subgroupOf W) := CFSG.Open.IsElemAbelian.subgroupOf hE W

end Elem

section HypOne

variable {G : Type} [Group G]

theorem ggAutK_hypOne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M E₀ K : Subgroup G}
    (hfus : GGControlsStrongFusion M E₀) (hE₀el : IsElemAbelian p E₀)
    (hE₀card : Nat.card E₀ = p ^ 2) (hEK : E₀ ≤ Subgroup.normalizer (K : Set G)) (hKM : ¬ K ≤ M)
    {W' : Type} [Group W'] (π : ↥(E₀ ⊔ K) →* W') (hπ : Function.Surjective π)
    (hker : π.ker ≤ ((E₀ ⊔ (K ⊓ M)) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf (E₀ ⊔ K)) :
    p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p ((E₀.subgroupOf (E₀ ⊔ K)).map π) ∧
      Nat.card ((E₀.subgroupOf (E₀ ⊔ K)).map π) = p ^ 2 ∧
      GGControlsStrongFusion (((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π)
        ((E₀.subgroupOf (E₀ ⊔ K)).map π) := by
  have hEC : ∀ e ∈ E₀, e ∈ Subgroup.centralizer (K : Set G) → e = 1 := by
    intro e he heK
    by_contra he1
    exact hKM fun k hk => hfus.centralizer_le he he1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp heK k hk))
  have hinj : Function.Injective (π.comp (E₀.subgroupOf (E₀ ⊔ K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    have h1 := Subgroup.mem_subgroupOf.mp (hker hs)
    have h2 := hEC _ (Subgroup.mem_subgroupOf.mp s.2) (Subgroup.mem_inf.mp h1).2
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h2)
  have hcard : Nat.card ((E₀.subgroupOf (E₀ ⊔ K)).map π) = p ^ 2 := by
    have hmap : (E₀.subgroupOf (E₀ ⊔ K)).map π =
        (π.comp (E₀.subgroupOf (E₀ ⊔ K)).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : E₀ ≤ E₀ ⊔ K)).toEquiv,
      hE₀card]
  refine ⟨hp, hp2, ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hE₀el _) π, hcard,
    ggControlsStrongFusion_iff.mpr ⟨Subgroup.map_mono fun w hw =>
      Subgroup.mem_subgroupOf.mpr
        ((le_sup_left : E₀ ≤ E₀ ⊔ (K ⊓ M)) (Subgroup.mem_subgroupOf.mp hw)), ?_⟩⟩
  intro e' he' he'1 g' hg'
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
  obtain ⟨w, rfl⟩ := hπ g'
  have hg'' : π (w⁻¹ * e * w) ∈ ((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π := by
    simpa [map_mul, map_inv] using hg'
  obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hg''
  have hk : h⁻¹ * (w⁻¹ * e * w) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπh, inv_mul_cancel]
  have hH : w⁻¹ * e * w ∈ (E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K) := by
    have h' := Subgroup.mul_mem _ hh (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hk))).1)
    rwa [mul_inv_cancel_left] at h'
  have hEM : E₀ ≤ M := hfus.1
  have hHM : E₀ ⊔ (K ⊓ M) ≤ M := sup_le hEM inf_le_right
  have heE : ((e : ↥(E₀ ⊔ K)) : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp he
  have he1 : ((e : ↥(E₀ ⊔ K)) : G) ≠ 1 := fun h1 => he'1 (by
    rw [show e = 1 from Subtype.ext h1, map_one])
  have hconj : ((w : ↥(E₀ ⊔ K)) : G)⁻¹ * (e : G) * (w : G) ∈ M := by
    have h' := hHM (Subgroup.mem_subgroupOf.mp hH)
    simpa using h'
  have hwM : ((w : ↥(E₀ ⊔ K)) : G) ∈ M := hfus.mem_of_conj_mem heE he1 hconj
  have hwW : ((w : ↥(E₀ ⊔ K)) : G) ∈ ((E₀ : Set G) * (K : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E₀ K hEK]
    exact w.2
  obtain ⟨e₁, he₁, k, hk', hek⟩ := Set.mem_mul.mp hwW
  have hkM : k ∈ M := by
    have h' := M.mul_mem (M.inv_mem (hEM he₁)) hwM
    rwa [← hek, inv_mul_cancel_left] at h'
  refine Subgroup.mem_map.mpr ⟨w, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
  rw [← hek]
  exact Subgroup.mul_mem _ (le_sup_left (a := E₀) he₁)
    (le_sup_right (a := E₀) (Subgroup.mem_inf.mpr ⟨hk', hkM⟩))

end HypOne

@[expose] def GGLemmaThreeThirteenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ X H E : Subgroup G,
    (∀ K L' : Subgroup G, K ≤ X → L' ≤ K → ∀ [(L'.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L'.subgroupOf K) → (∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a) →
        InCatalog (K ⧸ L'.subgroupOf K)) →
    IsElemAbelian p E → Nat.card E = p ^ 2 → GGControlsStrongFusionIn X H E →
      ∀ K : Subgroup G, IsComponentOf K X → ¬ K ≤ H → E ≤ Subgroup.normalizer (K : Set G)

section Inputs


end Inputs

end CFSG.StandardType
