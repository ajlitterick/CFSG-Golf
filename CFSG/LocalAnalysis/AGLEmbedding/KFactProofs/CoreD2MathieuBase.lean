
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2PermSound
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Data.CoreD2Mathieu
import CFSG.GroupTheory.ElementaryAbelianTransport

@[expose] public section

namespace CFSG.AGLEmbedding.CoreD2

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

@[expose] def CoreGenerationZOf (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ (E : Subgroup G) (Γ : Set G), IsPGroup p E ∧ Nat.card E = p ^ 3 ∧
    (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧ Subgroup.closure Γ = ⊤ ∧
    ∀ g ∈ Γ, (∃ Y : Subgroup G, Y ≤ E ∧ 2 ≤ Open.pRank p Y ∧
        g ∈ Subgroup.normalizer (Y : Set G)) ∨
      ∃ u ∈ E, u ≠ 1 ∧ u ^ p = 1 ∧ (∀ x ∈ E, x * u = u * x) ∧
        g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G)

section Abstract

variable {X : Type*} [Group X]

theorem mem_normalizer_zpowers_of_mul_eq [Finite X] {u g : X} {α : ℕ} (h : g * u = u ^ α * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup X) : Set X) := by
  have hcu : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
    rw [mul_inv_eq_iff_eq_mul.2 h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _
  have hle : Subgroup.zpowers u ≤ (Subgroup.zpowers u).comap (MulAut.conj g).toMonoidHom :=
    Subgroup.zpowers_le.2 hcu
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

theorem isElemAbelian_zpowers {p : ℕ} {u : X} (hu : u ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers u) := CFSG.Open.isElemAbelian_zpowers hu

theorem mem_of_central [Finite X] {p : ℕ} (hp : p.Prime) {E A : Subgroup X}
    (hEc : Nat.card E = p ^ 3) (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (hAE : A ≤ E)
    (hAe : IsElemAbelian p A) (hA : Nat.card A = p ^ 2) {u : X} (huE : u ∈ E)
    (hu : ∀ x ∈ E, x * u = u * x) : u ∈ A := by
  by_contra huA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hrc : ((A : Set X) ∪ {u}).Pairwise Commute := by
    rintro x (hx | hx) y (hy | hy) hxy
    · exact hcomm x hx y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hu x (hAE hx)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hu y (hAE hy)).symm
    · rw [Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  have hBcomm := Subgroup.isMulCommutative_closure hrc
  set B := Subgroup.closure ((A : Set X) ∪ {u}) with hB
  have hAB : A ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have huB : u ∈ B := Subgroup.subset_closure (Or.inr rfl)
  have hBE : B ≤ E := by
    rw [hB, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hAE hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact huE
  have hd1 : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hd2 : Nat.card B ∣ p ^ 3 := hEc ▸ Subgroup.card_dvd_of_le hBE
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow hp).1 hd2
  rw [hA, hm] at hd1
  have hm2 : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd1
  have hm' : m = 2 ∨ m = 3 := by omega
  rcases hm' with rfl | rfl
  · have : A = B := Subgroup.eq_of_le_of_card_ge hAB (by rw [hA, hm])
    exact huA (this ▸ huB)
  · have : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hEc, hm])
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    rw [← this] at hx hy
    exact hxy (congrArg Subtype.val (hBcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem glbCore_le_comap_conj [Finite X] (p k : ℕ) (hp : p.Prime) {P P' : Subgroup X} (l : X)
    (h : P.map (MulAut.conj l).toMonoidHom = P') :
    GLBCore p k P ≤ (GLBCore p k P').comap (MulAut.conj l).toMonoidHom := by
  refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p k _ _).mpr fun Q hQ hrank => ?_
  intro n hn
  rw [Subgroup.mem_comap]
  refine CFSG.AGLEmbeddingD2.normalizer_le_glbCore p k (Q := Q.map (MulAut.conj l).toMonoidHom)
    (by rw [← h]; exact Subgroup.map_mono hQ) ?_ ?_
  · rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _
      (MulAut.conj l).injective Q]
  · exact Subgroup.le_normalizer_map (MulAut.conj l).toMonoidHom ⟨n, hn, rfl⟩

theorem map_conj_inv_map_conj (P : Subgroup X) (l : X) :
    (P.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = P := by
  rw [Subgroup.map_map]
  have : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem coreGenerationZOf_of_gens [Finite X] {G : Subgroup X} {p : ℕ} (hp : p.Prime) {S : Set X}
    (hS : G = Subgroup.closure S) {E : Subgroup X} (hEp : IsPGroup p E)
    (hEc : Nat.card E = p ^ 3) (hEG : E ≤ G) (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x)
    {Γ : Set X} (hΓG : Γ ⊆ G) (hgen : S ⊆ Subgroup.closure Γ)
    (hΓ : ∀ g ∈ Γ,
      (∃ u v : X, u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧
        (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
          g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
      (∃ u ∈ E, u ≠ 1 ∧ u ^ p = 1 ∧ (∀ x ∈ E, x * u = u * x) ∧ ∃ α : ℕ, g * u = u ^ α * g)) :
    CoreGenerationZOf ↥G p := by
  refine ⟨E.subgroupOf G, {g : ↥G | (g : X) ∈ Γ}, hEp.comap_subtype, ?_, ?_, ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨⟨x, hEG hx⟩, Subgroup.mem_subgroupOf.2 hx, ⟨y, hEG hy⟩, Subgroup.mem_subgroupOf.2 hy,
      fun h => hxy (congrArg Subtype.val h)⟩
  · rw [eq_top_iff]
    intro h _
    have hmap : (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype = Subgroup.closure Γ := by
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
    rcases hΓ _ hg with ⟨u, v, huE, hvE, hu, hv, huv, hu1, hvu, α, β, γ, δ, h1, h2⟩ |
      ⟨u, huE, hu1, hu, hcent, α, h1⟩
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
      refine ⟨⟨u, hEG huE⟩, Subgroup.mem_subgroupOf.2 huE,
        fun h => hu1 (congrArg Subtype.val h), Subtype.ext (by simpa using hu), ?_,
        mem_normalizer_zpowers_of_mul_eq (α := α) (Subtype.ext (by simpa using h1))⟩
      intro x hx
      exact Subtype.ext (by simpa using hcent x (Subgroup.mem_subgroupOf.1 hx))

theorem glbCore_sup_of_coreGenerationZOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : CoreGenerationZOf G p) (hS : ∀ T : Sylow p G, Nat.card T = p ^ 3)
    (S : Sylow p G) (A : Subgroup G) (hAS : A ≤ (S : Subgroup G)) (hAe : IsElemAbelian p A)
    (hA : Nat.card A = p ^ 2) :
    GLBCore p 2 (S : Subgroup G) ⊔ GLBCore p 1 A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, Γ, hEp, hEc, hnc, hΓ, hnorm⟩ := h
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
  have hle : (⊤ : Subgroup G) ≤ GLBCore p 2 (T₀ : Subgroup G) ⊔
      GLBCore p 1 (A.map (MulAut.conj l).toMonoidHom) := by
    rw [← hΓ, Subgroup.closure_le]
    intro g hg
    rcases hnorm g hg with ⟨Y, hYE, hrank, hgY⟩ | ⟨u, huE, hu1, hu, hcent, hgu⟩
    · exact Subgroup.mem_sup_left (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 2
        (hYE.trans hET0.symm.le) hrank hgY)
    · have huA := mem_of_central hp hEc hnc hA' hAe' hAc' huE hcent
      have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf u = p := orderOf_eq_prime hu hu1
      have hr : 1 ≤ Open.pRank p (Subgroup.zpowers u) :=
        CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers hu)
          (by rw [Nat.card_zpowers, hord, pow_one])
      exact Subgroup.mem_sup_right (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1
        (Subgroup.zpowers_le.2 huA) hr hgu)
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

end Abstract

section Perm


end Perm

end CFSG.AGLEmbedding.CoreD2

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreD2Perm
  CFSG.Blueprint CFSG.Open

instance finite_carrier_M12 : Finite (NativeSporadic.Carrier .M12) :=
  inferInstanceAs (Finite NativeSporadic.M12)

abbrev m12CoreA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

abbrev m12CoreB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]


instance finite_carrier_M24 : Finite (NativeSporadic.Carrier .M24) :=
  inferInstanceAs (Finite NativeSporadic.M24)


theorem card_sylow_M24_three :
    ∀ T : Sylow 3 (NativeSporadic.Carrier .M24), Nat.card T = 3 ^ 3 := by
  intro T
  have hcard : Nat.card (NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  have h0 : (244823040 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 3 ^ 3 ∣ 244823040)
  have h2 : ¬ 4 ≤ (244823040 : ℕ).factorization 3 := fun h => by
    have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hcard, show (244823040 : ℕ).factorization 3 = 3 by omega]

end CFSG.AGLEmbedding
