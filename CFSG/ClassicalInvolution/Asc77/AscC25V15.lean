module

public import CFSG.ClassicalInvolution.Asc77.AscC25V14
public import CFSG.ClassicalInvolution.AschTight.S19CTop
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Ctx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

structure TwinCtx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) : Prop where
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : HypOmegaMod p f Ω
  hK : K ∈ Ω
  hK' : K' ∈ Ω
  hI : IsUniqueInvolution K z
  hI' : IsUniqueInvolution K' z
  ne : K' ≠ K
  htw : twinSet Ω K = {K, K'}
  hperp : KPerp Ω K = {K, K'}

namespace TwinCtx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem conj_K (d : TwinCtx p f Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K = K ∨ conjSub g K = K' := by
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  have h1 : conjSub g K ∈ twinSet Ω K :=
    ⟨d.hΩ.conjInvariant g K d.hK, z, d.hI, hgz ▸ d.hI.conj g⟩
  rw [d.htw] at h1
  exact h1

theorem conj_K' (d : TwinCtx p f Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K' = K ∨ conjSub g K' = K' := by
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  have h1 : conjSub g K' ∈ twinSet Ω K :=
    ⟨d.hΩ.conjInvariant g K' d.hK', z, d.hI, hgz ▸ d.hI'.conj g⟩
  rw [d.htw] at h1
  exact h1

theorem conj_iff (d : TwinCtx p f Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K = K ↔ conjSub g K' = K' := by
  constructor
  · intro h
    rcases d.conj_K' hg with h' | h'
    · exact absurd (conjSub_injective g (h'.trans h.symm)) d.ne
    · exact h'
  · intro h
    rcases d.conj_K hg with h' | h'
    · exact h'
    · exact absurd (conjSub_injective g (h'.trans h.symm)) d.ne.symm

theorem nbr (d : TwinCtx p f Ω K K' z) {J : Subgroup G} (h : J ∈ omegaNbr Ω K) :
    J ∈ twinSet Ω K := by
  have h1 : J ∈ KPerp Ω K := Or.inr h
  rw [d.hperp] at h1
  rcases h1 with rfl | rfl
  · exact absurd rfl h.2.1
  · rw [d.htw]
    exact Or.inr rfl

theorem conj_normalizer (d : TwinCtx p f Ω K K' z) {y x : G} (hy : y * z = z * y)
    (hx : x * z = z * x) (hxK : conjSub x K = K) : conjSub (y * x * y⁻¹) K = K := by
  have hyi : y⁻¹ * z = z * y⁻¹ := by
    have h1 : y * z = z * y := hy
    calc y⁻¹ * z = y⁻¹ * (z * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * z) * y⁻¹ := by rw [h1]
      _ = z * y⁻¹ := by group
  have hxK' : conjSub x K' = K' := (d.conj_iff hx).mp hxK
  have e1 : conjSub (y * x * y⁻¹) K = conjSub y (conjSub x (conjSub y⁻¹ K)) := by
    rw [conjSub_mul, conjSub_mul]
  rcases d.conj_K hyi with h | h
  · rw [e1, h, hxK]
    have h1 := congrArg (conjSub y) h
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    exact h1.symm
  · rw [e1, h, hxK']
    have h1 := congrArg (conjSub y) h
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    exact h1.symm

end TwinCtx

section FromHyp25

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem twinCtx'_of_hyp25 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') :
    TwinCtx p f Ω K' K z where
  hp2 := h.hp
  hq := h.hs.stand.five
  hΩ := h.hΩ
  hK := h.hK'
  hK' := h.hK
  hI := h.hz'
  hI' := h.hz
  ne := h.hs.hne.symm
  htw := by
    rw [twinSet_eq_of_mem_twinSet h.hz h.hs.hK', h.hs.twinSet_eq, Set.pair_comm]
  hperp := by
    rw [h.hs.perp_of_twin h.hs.hK', Set.pair_comm]

end FromHyp25

section Sec

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem fs_isUniqueInvolution_conjSub (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (perfectCoreIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI' := hI.conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI'.ne_one (congrArg Subtype.val h), Subtype.ext hI'.sq, fun y hy hy2 => ?_⟩
  rcases hI'.unique _ (le_conjSub_of_mem c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem fs_isUniqueInvolution_secImg (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a)))
      (QuotientGroup.mk' _ ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
        (fs_isUniqueInvolution_conjSub hI hzA hzKa c).mem⟩) :=
  isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
    (isUniqueInvolution_subgroupOf (fs_isUniqueInvolution_conjSub hI hzA hzKa c)
      (le_conjGen ⟨c, rfl⟩))


theorem fs_false_of_le_normalizer (d : TwinCtx p f Ω K K' z) {a : G}
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (htwin : conjSub c₂ K ∉ twinSet Ω (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀)
    (hRle : R₀ ≤ conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) : Subgroup G) :
        Set G)) : False := by
  have hI := d.hI
  have hΩ := d.hΩ
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hJ₁ : conjSub c₁ K ∈ Ω := hΩ.conjInvariant c₁ K d.hK
  have hJ₂ : conjSub c₂ K ∈ Ω := hΩ.conjInvariant c₂ K d.hK
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hJne : conjSub c₁ K ≠ conjSub c₂ K := fun h => hne (conjSub_perfectCore_eq hc₁ hc₂ h)
  have hRz : R₀ ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
      (Subgroup.mem_normalizer_iff.mp (hRN hx) _).mp (conj_mem_conjSub hzKa)
    have h2 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈ conjSub c₁ K := Subgroup.map_mono hKaK h1
    have h3 : x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) = 1 := by
      calc x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) =
          x * ((c₁ * z * c₁⁻¹) * (c₁ * z * c₁⁻¹)) * x⁻¹ := by group
        _ = 1 := by rw [hI₁.sq]; group
    rcases hI₁.unique _ h2 h3 with h | h
    · exfalso
      apply hI₁.ne_one
      calc c₁ * z * c₁⁻¹ = x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (c₁ * z * c₁⁻¹) = x * (c₁ * z * c₁⁻¹) * x⁻¹ * x := by group
        _ = c₁ * z * c₁⁻¹ * x := by rw [h]
  have hRJ₂ : R₀ ≤ conjSub c₂ K := hRle.trans (Subgroup.map_mono hKaK)
  obtain ⟨V₀, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRJ₂ hRz)
  have hz₂V : c₂ * z * c₂⁻¹ ∈ V₀ := hRV (mem_of_le_member hI₂ hRJ₂ hR2 (by omega))
  have hcard : Nat.card R₀ ≤ Nat.card V₀ := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f d.hp2 d.hq G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI₂ V₀ hV hz₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, hVc⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · have hVJ₂ : V₀ ≤ conjSub c₂ K := hV.1.trans inf_le_left
    have hVN : V₀ ≤ Subgroup.normalizer (conjSub c₁ K : Set G) :=
      le_normalizer_of_commutator_le (hVc.trans (oddCoreOf_le_self _))
    have hnbr : conjSub c₂ K ∈ omegaNbr Ω (conjSub c₁ K) :=
      ⟨hJ₂, hJne.symm, V₀, hV4, hVJ₂, hVN⟩
    have h1 := omegaNbr_conj hΩ.conjInvariant hnbr c₁⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := d.nbr h1
    have h3 := twinSet_conj hΩ.conjInvariant h2 c₁
    rw [conjSub_conjSub_inv] at h3
    exact htwin h3


end Sec

end CFSG.ClassicalInvolution.Asc77.C25V
