module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Elementary

variable {G : Type*} [Group G]

theorem ggF4_normalizer_inf_le (H K : Subgroup G) :
    Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.mp hm.1 z
  have h2 := Subgroup.mem_normalizer_iff.mp hm.2 z
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

theorem ggF4_false_of_pow_le {p k m : ℕ} (hp : p.Prime) (hk : k < 4) (h4 : p ^ 4 ≤ m)
    (hm : m ≤ p ^ k) : False :=
  absurd (h4.trans hm) (not_le.mpr (pow_lt_pow_right₀ hp.one_lt hk))

theorem ggF4_orderOf_eq_of_elemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) : orderOf b = p := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hE.2 b hb)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hb1
  · exact h

theorem ggF4_exists_involution_of_card_le_two [Finite G] {U : Subgroup G} (hU : U ≠ ⊥)
    (hU2 : Nat.card U ≤ 2) : ∃ s ∈ U, orderOf s = 2 ∧ U = Subgroup.zpowers s := by
  obtain ⟨s, hsU, hs1⟩ : ∃ s ∈ U, s ≠ 1 := by
    by_contra h
    push Not at h
    exact hU ((Subgroup.eq_bot_iff_forall U).mpr h)
  have hdvd : orderOf s ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hsU
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hle : orderOf s ≤ 2 := (Nat.le_of_dvd hpos hdvd).trans hU2
  have hne : orderOf s ≠ 1 := fun h => hs1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf s = 2 := by
    have h0 : 0 < orderOf s := orderOf_pos s
    omega
  refine ⟨s, hsU, hord, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsU) ?_).symm
  rw [Nat.card_zpowers, hord]
  exact hU2

end Elementary

section Normalizer

variable {G : Type*} [Group G] {G₀ : Subgroup G}

theorem ggF4_normalizerMonoidHom_injective (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) :
    Function.Injective G₀.normalizerMonoidHom := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC]
  ext x
  simp

theorem ggF4_normalizerMonoidHom_of_mem (g : G₀) :
    G₀.normalizerMonoidHom ⟨g, Subgroup.le_normalizer g.2⟩ = MulAut.conj g := by
  have hφapp : ∀ (m : Subgroup.normalizer (G₀ : Set G)) (h : G₀),
      ((G₀.normalizerMonoidHom m h : G₀) : G) = (m : G) * h * (m : G)⁻¹ := fun _ _ => rfl
  ext h
  rw [MulAut.conj_apply, hφapp]
  rfl

theorem ggF4_card_le_two_of_inf_eq_bot (hC : Subgroup.centralizer (G₀ : Set G) = ⊥)
    (hQ : ∀ Q : Subgroup (MulAut G₀), IsPGroup 2 Q →
      Q ⊓ (MulAut.conj : G₀ →* MulAut G₀).range = ⊥ → Nat.card Q ≤ 2)
    {U : Subgroup G} (hUN : U ≤ Subgroup.normalizer (G₀ : Set G)) (hU2 : IsPGroup 2 U)
    (hUG : U ⊓ G₀ = ⊥) : Nat.card U ≤ 2 := by
  classical
  set N := Subgroup.normalizer (G₀ : Set G)
  set φ := G₀.normalizerMonoidHom
  have hφ : Function.Injective φ := ggF4_normalizerMonoidHom_injective hC
  have hcard : Nat.card ((U.subgroupOf N).map φ) = Nat.card U := by
    rw [Subgroup.card_map_of_injective hφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  rw [← hcard]
  refine hQ _ ((hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm).map φ) ?_
  rw [eq_bot_iff]
  rintro σ ⟨⟨u, hu, rfl⟩, ⟨g, hg⟩⟩
  have hug : u = ⟨g, Subgroup.le_normalizer g.2⟩ := by
    apply hφ
    rw [← hg, ggF4_normalizerMonoidHom_of_mem]
  have hu1 : (u : G) ∈ U ⊓ G₀ := ⟨hu, by rw [hug]; exact g.2⟩
  rw [hUG, Subgroup.mem_bot] at hu1
  have hu1' : u = 1 := Subtype.ext hu1
  rw [Subgroup.mem_bot, hu1', map_one]

theorem ggF4_exists_involution_of_even [Finite G] (hC : Subgroup.centralizer (G₀ : Set G) = ⊥)
    {X : Subgroup G} (hGX : G₀ ≤ X) (hXN : X ≤ Subgroup.normalizer (G₀ : Set G))
    (heven : Even (G₀.relIndex X)) {C : Subgroup (MulAut G₀)}
    (hIC : ∀ σ : MulAut G₀, ∃ i ∈ (MulAut.conj : G₀ →* MulAut G₀).range, ∃ c ∈ C, σ = i * c)
    (hIC' : (MulAut.conj : G₀ →* MulAut G₀).range ⊓ C = ⊥) :
    ∃ s ∈ X, s ∉ G₀ ∧ orderOf s = 2 := by
  classical
  set N := Subgroup.normalizer (G₀ : Set G)
  set φ := G₀.normalizerMonoidHom
  have hφ : Function.Injective φ := ggF4_normalizerMonoidHom_injective hC
  set K := (MulAut.conj : G₀ →* MulAut G₀).range
  have hKn : K.Normal := ggSix_conj_range_normal
  have hKmap : (G₀.subgroupOf N).map φ = K := by
    ext σ
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, (ggF4_normalizerMonoidHom_of_mem ⟨(m : G), hm⟩).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.le_normalizer g.2⟩, g.2, ggF4_normalizerMonoidHom_of_mem g⟩
  set X' := (X.subgroupOf N).map φ
  have hKX : K ≤ X' := by
    rw [← hKmap]
    exact Subgroup.map_mono fun m hm => hGX hm
  have heven' : Even (K.relIndex X') := by
    rw [← hKmap, Subgroup.relIndex_map_map_of_injective _ _ hφ,
      Subgroup.relIndex_subgroupOf hXN]
    exact heven
  have hodd : Odd (K.relIndex K) := by
    rw [Subgroup.relIndex_self]
    exact odd_one
  obtain ⟨σ, hσX, hσ2, hσK, -⟩ :=
    ggSix_exists_conj_involution_of_even hKn le_rfl hodd hIC hIC' hKX heven'
  obtain ⟨m, hmX, rfl⟩ := hσX
  refine ⟨m, hmX, ?_, ?_⟩
  · intro hmG
    apply hσK
    rw [← hKmap]
    exact ⟨m, hmG, rfl⟩
  · rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφ m, hσ2]

end Normalizer

section Inputs

@[expose] def GGF4Config {G : Type} [Group G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G)
    (G₀ : Subgroup G) : Prop :=
  StatedLieAdmissible .F4 n 2 f ∧ 2 ≤ (ggU .F4 n f).D.rank ∧ ψ.range = G₀ ∧
    ψ.ker ≤ Subgroup.center (ggU .F4 n f).K ∧ commutator ↥G₀ = ⊤ ∧
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 f ∧ Subgroup.centralizer (G₀ : Set G) = ⊥

@[expose] def GGF4AutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f →
      ∃ C : Subgroup (MulAut G₀),
        (∀ σ : MulAut G₀, ∃ i ∈ (MulAut.conj : G₀ →* MulAut G₀).range, ∃ c ∈ C, σ = i * c) ∧
        (MulAut.conj : G₀ →* MulAut G₀).range ⊓ C = ⊥ ∧
        ∀ Q : Subgroup (MulAut G₀), IsPGroup 2 Q →
          Q ⊓ (MulAut.conj : G₀ →* MulAut G₀).range = ⊥ → Nat.card Q ≤ 2

@[expose] def GGF4InnerDiagInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → ∀ b ∈ Subgroup.normalizer (G₀ : Set G),
      GGPsiInnerDiag (ggU .F4 n f).D ψ b → b ∈ G₀


@[expose] def GGF4TwoLocalRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 →
    ∀ R : Subgroup G, R ≤ G₀ → R ≠ ⊥ → IsPGroup 2 R →
      ∀ E : Subgroup G, E ≤ G₀ → E ≤ Subgroup.normalizer (R : Set G) → IsElemAbelian p E →
        Nat.card E ≤ p ^ 3


@[expose] def GGF4GraphFieldCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f → ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ →
    orderOf s = 2 → ∀ Q : Subgroup G, Q ≤ G₀ ⊓ Subgroup.centralizer {s} → IsPGroup 2 Q →
      G₀ ⊓ Subgroup.centralizer {s} ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥


end Inputs

end CFSG.StandardType
