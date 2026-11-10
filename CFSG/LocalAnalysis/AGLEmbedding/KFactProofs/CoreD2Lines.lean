
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2MathieuBase
public import Certificates.Data.CoreD2Lines

public section

namespace CFSG.AGLEmbedding.CoreD2

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

@[expose] def CoreGenerationVOf (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ E : Subgroup G, IsPGroup p E ∧ Nat.card E = p ^ 3 ∧
    ∀ A : Subgroup G, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set G, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
        (∃ Y : Subgroup G, Y ≤ E ∧ 2 ≤ Open.pRank p Y ∧
          g ∈ Subgroup.normalizer (Y : Set G)) ∨
        ∃ Q : Subgroup G, Q ≤ A ∧ 1 ≤ Open.pRank p Q ∧ g ∈ Subgroup.normalizer (Q : Set G)

section Abstract

variable {X : Type*} [Group X]

theorem wordVal_mem_of (S : List X) (H : Subgroup X) :
    ∀ w : List ℤ, (∀ l ∈ w, S.getD (l.natAbs - 1) 1 ∈ H) → wordVal S w ∈ H
  | [], _ => H.one_mem
  | l :: w, h => by
    rw [wordVal]
    refine H.mul_mem ?_ (wordVal_mem_of S H w fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hl := h l List.mem_cons_self
    split_ifs with hpos
    · rwa [show l.toNat = l.natAbs by omega]
    · exact H.inv_mem (by rwa [show (-l).toNat = l.natAbs by omega])

theorem card_closure_pair_of_pow [Finite X] {p : ℕ} (hp : p.Prime) {u v : X} (hu : u ^ p = 1)
    (hv : v ^ p = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hvu : ∀ j < p, v ≠ u ^ j) :
    Nat.card ↥(Subgroup.closure ({u, v} : Set X)) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hou : orderOf u = p := orderOf_eq_prime hu hu1
  have hv1 : v ≠ 1 := by simpa using hvu 0 hp.pos
  have hov : orderOf v = p := orderOf_eq_prime hv hv1
  have hind : v ∉ Subgroup.zpowers u := by
    intro hmem
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
    obtain ⟨m, hm⟩ := hmem
    refine hvu (m % p) (Nat.mod_lt m hp.pos) ?_
    rw [← hou, pow_mod_orderOf, hm]
  exact card_closure_pair hp huv hou hov hind

theorem coreGenerationVOf_of_gens [Finite X] {G : Subgroup X} {p : ℕ} (hp : p.Prime) {S : Set X}
    (hS : G = Subgroup.closure S) {E : Subgroup X} (hEp : IsPGroup p E)
    (hEc : Nat.card E = p ^ 3) (hEG : E ≤ G)
    (hΓ : ∀ A : Subgroup X, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set X, Γ ⊆ G ∧ S ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
        (∃ u v : X, u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧
          (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
            g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
        (∃ y ∈ A, y ≠ 1 ∧ y ^ p = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g)) :
    CoreGenerationVOf ↥G p := by
  refine ⟨E.subgroupOf G, hEp.comap_subtype, ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  · intro A' hA'E hA'e hA'c
    set A : Subgroup X := A'.map G.subtype with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hA'E hx)
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective G.subtype_injective, hA'c]
    obtain ⟨Γ, hΓG, hgen, hnorm⟩ := hΓ A hAE hAe hAc
    refine ⟨{g : ↥G | (g : X) ∈ Γ}, ?_, ?_⟩
    · rw [eq_top_iff]
      intro h _
      have hmap : (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype =
          Subgroup.closure Γ := by
        rw [MonoidHom.map_closure]
        congr 1
        ext z
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact hg
        · intro hz
          exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
      have hle : G ≤ (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype := by
        rw [hmap, hS, Subgroup.closure_le]
        exact hgen
      obtain ⟨k, hk, hkh⟩ := hle h.2
      have : k = h := Subtype.ext hkh
      rwa [← this]
    · intro g hg
      rcases hnorm _ hg with ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, α, β, γ, δ, h1, h2⟩ |
        ⟨y, hyA, hy1, hy, α, h1⟩
      · left
        set u' : ↥G := ⟨u, hEG huE⟩ with hu'
        set v' : ↥G := ⟨v, hEG hvE⟩ with hv'
        refine ⟨Subgroup.closure ({u', v'} : Set ↥G), ?_, ?_, ?_⟩
        · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
          exact ⟨Subgroup.mem_subgroupOf.2 huE, Subgroup.mem_subgroupOf.2 hvE⟩
        · refine two_le_pRank_closure_pair hp ?_ ?_ ?_ ?_ ?_
          · exact Subtype.ext (by simpa [hu'] using hu)
          · exact Subtype.ext (by simpa [hv'] using hv)
          · exact Subtype.ext (by simpa [hu', hv'] using huv)
          · exact fun h => hu1 (congrArg Subtype.val h)
          · intro j hj h
            exact hvu j hj (by simpa [hu', hv'] using congrArg Subtype.val h)
        · exact mem_normalizer_closure_pair (α := α) (β := β) (γ := γ) (δ := δ)
            (Subtype.ext (by simpa [hu', hv'] using h1))
            (Subtype.ext (by simpa [hu', hv'] using h2))
      · right
        obtain ⟨y', hy'A, rfl⟩ := Subgroup.mem_map.1 hyA
        have hy'p : y' ^ p = 1 := Subtype.ext (by simpa using hy)
        have hy'1 : y' ≠ 1 := fun h => hy1 (by simpa using congrArg Subtype.val h)
        have : Fact p.Prime := ⟨hp⟩
        have hord : orderOf y' = p := orderOf_eq_prime hy'p hy'1
        refine ⟨Subgroup.zpowers y', Subgroup.zpowers_le.2 hy'A, ?_,
          mem_normalizer_zpowers_of_mul_eq (α := α) (Subtype.ext (by simpa using h1))⟩
        exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers hy'p)
          (by rw [Nat.card_zpowers, hord, pow_one])

theorem glbCore_sup_of_coreGenerationVOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : CoreGenerationVOf G p) (hS : ∀ T : Sylow p G, Nat.card T = p ^ 3)
    (S : Sylow p G) (A : Subgroup G) (hAS : A ≤ (S : Subgroup G)) (hAe : IsElemAbelian p A)
    (hA : Nat.card A = p ^ 2) :
    GLBCore p 2 (S : Subgroup G) ⊔ GLBCore p 1 A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEp, hEc, hall⟩ := h
  obtain ⟨T₀, hET⟩ := hEp.exists_le_sylow
  have hET0 : (T₀ : Subgroup G) = E :=
    (Subgroup.eq_of_le_of_card_ge hET (by rw [hEc, hS T₀])).symm
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (S : Subgroup G) ≤ ⊤) le_top S.isPGroup' T₀.isPGroup'
    (by
      change ¬ p ∣ (S : Subgroup G).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity T₀, Sylow.card_eq_multiplicity S])
  have hA' : A.map (MulAut.conj l).toMonoidHom ≤ E := by
    rw [← hET0, ← hl]
    exact Subgroup.map_mono hAS
  have hAe' : IsElemAbelian p (A.map (MulAut.conj l).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hAe _
  have hAc' : Nat.card (A.map (MulAut.conj l).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hA]
  obtain ⟨Γ, hΓ, hnorm⟩ := hall _ hA' hAe' hAc'
  have hle : (⊤ : Subgroup G) ≤ GLBCore p 2 (T₀ : Subgroup G) ⊔
      GLBCore p 1 (A.map (MulAut.conj l).toMonoidHom) := by
    rw [← hΓ, Subgroup.closure_le]
    intro g hg
    rcases hnorm g hg with ⟨Y, hYE, hrank, hgY⟩ | ⟨Q, hQA, hrank, hgQ⟩
    · exact Subgroup.mem_sup_left (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2
        (hYE.trans hET0.symm.le) hrank hgY)
    · exact Subgroup.mem_sup_right (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 hQA hrank hgQ)
  have hTS : (T₀ : Subgroup G).map (MulAut.conj l⁻¹).toMonoidHom = S := by
    rw [← hl, map_conj_inv_map_conj]
  have hAA : (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = A :=
    map_conj_inv_map_conj A l
  have h2 := glbCore_le_comap_conj p 2 hp l⁻¹ hTS
  have h1 := glbCore_le_comap_conj p 1 hp l⁻¹ hAA
  have hle' : (⊤ : Subgroup G) ≤ (GLBCore p 2 (S : Subgroup G) ⊔ GLBCore p 1 A).comap
      (MulAut.conj l⁻¹).toMonoidHom :=
    hle.trans (sup_le (h2.trans (Subgroup.comap_mono le_sup_left))
      (h1.trans (Subgroup.comap_mono le_sup_right)))
  rw [eq_top_iff]
  intro x _
  have hx := hle' (Subgroup.mem_top (l * x * l⁻¹))
  rw [Subgroup.mem_comap] at hx
  simpa [MulAut.conj_apply, mul_assoc] using hx

theorem coreGenerationVOf_of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (e : G ≃* H) (h : CoreGenerationVOf G p) :
    CoreGenerationVOf H p := by
  obtain ⟨E, hEp, hEc, hall⟩ := h
  refine ⟨E.map e.toMonoidHom, hEp.map e.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hEc]
  · intro A' hA'E hA'e hA'c
    set A : Subgroup G := A'.map e.symm.toMonoidHom with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (hA'E hy)
      have : e.symm.toMonoidHom y = x := by
        rw [← hxy]
        exact e.symm_apply_apply x
      rwa [this]
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective e.symm.injective, hA'c]
    obtain ⟨Γ, hΓ, hnorm⟩ := hall A hAE hAe hAc
    refine ⟨e.toMonoidHom '' Γ, ?_, ?_⟩
    · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro _ ⟨g, hg, rfl⟩
      rcases hnorm g hg with ⟨Y, hYE, hrank, hgY⟩ | ⟨Q, hQA, hrank, hgQ⟩
      · left
        refine ⟨Y.map e.toMonoidHom, Subgroup.map_mono hYE, ?_, ?_⟩
        · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Y)
        · rw [← Subgroup.map_equiv_normalizer_eq]
          exact Subgroup.mem_map_of_mem _ hgY
      · right
        refine ⟨Q.map e.toMonoidHom, ?_, ?_, ?_⟩
        · rintro _ ⟨q, hq, rfl⟩
          obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 (hQA hq)
          have : e.toMonoidHom q = x := by
            rw [← hxq]
            exact e.apply_symm_apply x
          rwa [this]
        · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Q)
        · rw [← Subgroup.map_equiv_normalizer_eq]
          exact Subgroup.mem_map_of_mem _ hgQ

end Abstract

section Perm


end Perm

end CFSG.AGLEmbedding.CoreD2
