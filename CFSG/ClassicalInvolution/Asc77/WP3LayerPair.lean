module

public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyPair

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K : Subgroup G}

abbrev exactLayer (Ω : Set (Subgroup G)) (c : G) : Subgroup G :=
  centLayer (exactFamily Ω c) c

abbrev exactPair (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup ↥(exactLayer Ω c)) :=
  restrictFamily (exactFamily Ω c) (exactLayer Ω c)

theorem exactFamily_eq_empty_of_not_nonempty (hne : ¬ (tqMembers Ω c).Nonempty) :
    exactFamily Ω c = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨K, hK, _⟩ => hne ⟨K, hK⟩

theorem centMembers_exactFamily (Ω : Set (Subgroup G)) (c : G) :
    centMembers (exactFamily Ω c) c = exactFamily Ω c := by
  ext K'
  exact ⟨fun h => h.1, fun h => ⟨h, le_centralizer_of_mem_exactFamily h⟩⟩

theorem exactLayer_eq_iSup (Ω : Set (Subgroup G)) (c : G) :
    exactLayer Ω c = ⨆ K' ∈ exactFamily Ω c, K' := by
  unfold exactLayer centLayer
  rw [centMembers_exactFamily]

theorem exactCore_le_exactLayer (hK : K ∈ tqMembers Ω c) : exactCore c K ≤ exactLayer Ω c :=
  le_centLayer ⟨exactCore_mem_exactFamily hK, exactCore_le_centralizer c K⟩

theorem exactLayer_le_centralizer (Ω : Set (Subgroup G)) (c : G) :
    exactLayer Ω c ≤ Subgroup.centralizer ({c} : Set G) :=
  centLayer_le fun _ hL => hL.2

theorem normalizesLayer_exactFamily (hΩ : ConjInvariant Ω) :
    NormalizesLayer (exactFamily Ω c) c := by
  have key : ∀ n : G, n ∈ Subgroup.centralizer ({c} : Set G) →
      exactLayer Ω c ≤ conjSub n⁻¹ (exactLayer Ω c) := by
    intro n hn
    refine centLayer_le fun L hL => ?_
    have hLc : conjSub n L ∈ centMembers (exactFamily Ω c) c :=
      ⟨conjSub_mem_exactFamily hΩ hn hL.1, le_centralizer_of_mem_exactFamily
        (conjSub_mem_exactFamily hΩ hn hL.1)⟩
    have h1 := conjSub_mono (n := n⁻¹) (le_centLayer hLc)
    rwa [conjSub_inv_conjSub] at h1
  intro n hn
  have h1 := key n hn
  have h2 := key n⁻¹ (inv_mem hn)
  rw [inv_inv] at h2
  have h3 : conjSub n (exactLayer Ω c) ≤ exactLayer Ω c := by
    have := conjSub_mono (n := n) h1
    rwa [conjSub_conjSub_inv] at this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (le_antisymm h3 h2)

theorem conjSub_exactLayer (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) :
    conjSub n (exactLayer Ω c) = exactLayer Ω c :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizesLayer_exactFamily hΩ n hn)


theorem exactLayer_ne_top (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) : exactLayer Ω c ≠ ⊤ := by
  intro h
  apply hnc
  rw [← Subgroup.centralizer_eq_top_iff_subset]
  exact top_le_iff.mp (h ▸ exactLayer_le_centralizer Ω c)

theorem card_exactLayer_lt (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) :
    Nat.card (exactLayer Ω c) < Nat.card G := by
  have h := Subgroup.card_mul_index (exactLayer Ω c)
  have hidx : (exactLayer Ω c).index ≠ 1 := fun h1 =>
    exactLayer_ne_top hnc (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card (exactLayer Ω c) := Nat.card_pos
  have hidx0 : (exactLayer Ω c).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ (exactLayer Ω c).index := by omega
  nlinarith


end Layer

section Lie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K : Subgroup G} {z : G}

abbrev exactImages (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup (OddQuot c)) :=
  memberImages (exactFamily Ω c) c

abbrev exactJoin (Ω : Set (Subgroup G)) (c : G) : Subgroup (OddQuot c) :=
  memberJoin (exactFamily Ω c) c

theorem exactJoin_normal (hΩ : ConjInvariant Ω) : (exactJoin Ω c).Normal :=
  memberJoin_normal_of_normalizes (normalizesLayer_exactFamily hΩ)

theorem modOdd_le_exactJoin {K' : Subgroup G} (hK' : K' ∈ exactFamily Ω c) :
    modOdd c K' ≤ exactJoin Ω c :=
  le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers (exactFamily Ω c) c) => modOdd c K) K'
    ⟨hK', le_centralizer_of_mem_exactFamily hK'⟩

theorem exists_big_decomposition_of_not_nonempty (hne : ¬ (tqMembers Ω c).Nonempty) :
    ∃ D : LieDecomposition (exactImages Ω c) (exactJoin Ω c), D.Big := by
  have hfam := exactFamily_eq_empty_of_not_nonempty hne
  refine ⟨{ ι := PEmpty
            Q := fun i => i.elim
            quasisimple := fun i => i.elim
            commute := fun i => i.elim
            iSup_eq := ?_
            exists_le := ?_
            rankOne_or_lie := fun i => i.elim }, fun i => i.elim⟩
  · refine le_antisymm (iSup_le fun i => i.elim) (iSup₂_le fun K' hK' => ?_)
    exact absurd hK'.1 (by rw [hfam]; exact Set.notMem_empty K')
  · rintro _ ⟨K', hK', rfl⟩
    exact absurd hK'.1 (by rw [hfam]; exact Set.notMem_empty K')

theorem lieDecomposition_exactFamily (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hBelow : CITBelowU p f (Nat.card G)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) :
    Nonempty (LieDecomposition (exactImages Ω c) (exactJoin Ω c)) := by
  by_cases hne : (tqMembers Ω c).Nonempty
  · have hs := secData_exactFamily hΩ hcls hc2 hne
    obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
    obtain ⟨D, -, -⟩ := hs.lieDecomposition_comp hp2 h0 hA1 hq Dsys
    exact ⟨D⟩
  · obtain ⟨D, -⟩ := exists_big_decomposition_of_not_nonempty hne
    exact ⟨D⟩


theorem oddQuotMk_centralizes_modOdd_exactCore {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z c : G}
    (hK : IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcK : c ∈ trivialOnQuot K) {b : G} (hb : b ∈ trivialOnQuot K)
    (hbc : b ∈ Subgroup.centralizer ({c} : Set G))
    (hq : CFSG.Open.IsQuasisimple ↥(modOdd c (exactCore c K))) :
    ∀ y ∈ modOdd c (exactCore c K),
      oddQuotMk c ⟨b, hbc⟩ * y = y * oddQuotMk c ⟨b, hbc⟩ :=
  oddQuotMk_centralizes_of_commutator_mem (exactCore_le_centralizer c K) hbc hq fun _ hl =>
    commutator_mem_oddCoreIn_triangleResidual hb hbc (axisResidual_exactCore hK hc2 hcK) hl


end Lie

section Compare

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K : Subgroup G}

theorem centMembers_subset_tqMembers : centMembers Ω c ⊆ tqMembers Ω c := fun _ hK =>
  ⟨hK.1, mem_trivialOnQuot_of_le_centralizer hK.2⟩

omit [Finite G] in
theorem exactCore_eq_self_of_mem_centMembers (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hK : K ∈ centMembers Ω c) : exactCore c K = K := by
  obtain ⟨z, hz⟩ := hcls K hK.1
  exact exactCore_eq_self hz.perfect hK.2

theorem centMembers_subset_exactFamily (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) :
    centMembers Ω c ⊆ exactFamily Ω c := fun _ hK =>
  ⟨_, centMembers_subset_tqMembers hK, (exactCore_eq_self_of_mem_centMembers hcls hK).symm⟩

theorem centLayer_le_exactLayer (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) :
    centLayer Ω c ≤ exactLayer Ω c :=
  centLayer_le fun _ hK => le_centLayer ⟨centMembers_subset_exactFamily hcls hK, hK.2⟩


theorem tqMembers_eq_centMembers_of_exact (hex : ExactMembers Ω) :
    tqMembers Ω c = centMembers Ω c := by
  ext L
  refine ⟨fun hL => ⟨hL.1, fun x hx => ?_⟩,
    fun hL => ⟨hL.1, mem_trivialOnQuot_of_le_centralizer hL.2⟩⟩
  have h1 : ⁅c, x⁆ ∈ oddCoreIn L := hL.2.2 x hx
  have h2 : oddCoreIn L = ⊥ := by
    show (classicalInvolutionOddCore ↥L).map L.subtype = ⊥
    rw [hex L hL.1, Subgroup.map_bot]
  rw [h2, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem exactFamily_eq_centMembers_of_exact (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) : exactFamily Ω c = centMembers Ω c := by
  refine Set.Subset.antisymm ?_ (centMembers_subset_exactFamily hcls)
  rintro _ ⟨K, hK, rfl⟩
  have hK' : K ∈ centMembers Ω c := by
    rw [← tqMembers_eq_centMembers_of_exact hex]
    exact hK
  have e : exactCore c K = K := exactCore_eq_self_of_mem_centMembers hcls hK'
  change exactCore c K ∈ centMembers Ω c
  rw [e]
  exact hK'

end Compare

end CFSG.ClassicalInvolution.Asc77.ExactLayer
