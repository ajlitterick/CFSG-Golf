module

public import CFSG.ClassicalInvolution.Asc77.AscE184Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem isSylow2In_inf_of_le_normalizer {V X Y : Subgroup G} (hV : IsSylow2In V X) (hYX : Y ≤ X)
    (hn : X ≤ Subgroup.normalizer (Y : Set G)) : IsSylow2In (V ⊓ Y) Y := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, ?_⟩
  intro T hTY hT2 hle
  obtain ⟨V', hV', hTV'⟩ := IsSylow2In.exists_ge hT2 (hTY.trans hYX)
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥X) (AscQuot.sylowOfIsSylow2In' hV)
    (AscQuot.sylowOfIsSylow2In' hV')
  have hVx : conjSub (x : G) V ≤ X := by
    have := conjSub_mono (n := (x : G)) hV.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have hV'eq : V' = conjSub (x : G) V := by
    have h1 : (conjSub (x : G) V).subgroupOf X = V'.subgroupOf X := by
      rw [← conjSub_subgroupOf X x V]
      exact hx
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hVx, inf_eq_left.mpr hV'.1, eq_comm] at h2
  have hxY : conjSub (x : G)⁻¹ Y = Y :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (Y : Set G)).inv_mem (hn x.2))
  have hTV : conjSub (x : G)⁻¹ T ≤ V ⊓ Y := by
    refine le_inf ?_ ?_
    · have := conjSub_mono (n := (x : G)⁻¹) (hTV'.trans hV'eq.le)
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_mono (n := (x : G)⁻¹) hTY
      rwa [hxY] at this
  have hcard : Nat.card T ≤ Nat.card ↥(V ⊓ Y) := by
    have h1 : Nat.card ↥(conjSub (x : G)⁻¹ T) = Nat.card T :=
      (Nat.card_congr (Subgroup.equivMapOfInjective T (MulAut.conj (x : G)⁻¹).toMonoidHom
        (MulAut.conj (x : G)⁻¹).injective).toEquiv).symm
    rw [← h1]
    exact Subgroup.card_le_of_le hTV
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

section Hull

variable {X : Subgroup G}


end Hull

variable (p f)


@[expose] def E18_4C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ A : Subgroup G, IsPGroup 2 A → R ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ →
          IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
            (Subgroup.centralizer (A : Set G)) → Subgroup.centralizer (A : Set G) ≤ H

omit [Finite G] in
private theorem centralizer_zpowers_eq_singleton (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  ext y
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute x y from h) k).eq


theorem e18_5_of_layer (h3 : E18_3 p f) (h69 : L6_9 p f) (h611 : L6_11 p f) : E18_5 p f := by
  intro G _ _ Ω K S R W H c
  by_contra hX
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hEA : EtaAbelian Ω := EtaAbelian.of_l6_9 h69 hp hq hΩ
  have hEM : EtaMeet Ω := EtaMeet.of_l6_11 h611 hp hq hΩ
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hKX : K ≤ ⨆ J ∈ Ω, J := le_iSup₂_of_le K c.stand.mem le_rfl
  have hK'X : K' ≤ ⨆ J ∈ Ω, J := le_iSup₂_of_le K' hK'tw.1 le_rfl
  have hnorm : (⨆ J ∈ Ω, J : Subgroup G).Normal := omegaGen_normal hΩ.conjInvariant
  have hgen : (⨆ J ∈ Ω, J : Subgroup G) ≤ ⨆ J ∈ {J | J ∈ Ω ∧ J ≤ (⨆ J ∈ Ω, J : Subgroup G)}, J :=
    iSup₂_le fun J hJ => le_iSup₂_of_le J ⟨hJ, le_iSup₂_of_le J hJ le_rfl⟩ le_rfl
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ (⨆ J ∈ Ω, J : Subgroup G))
      (⨆ J ∈ Ω, J : Subgroup G) := by
    refine isSylow2In_inf_of_le_normalizer ?_ le_top ?_
    · exact ⟨le_top, S.isPGroup', fun V' _ hV'2 hSV' => (S.is_maximal' hV'2 hSV')⟩
    · intro x _
      have := hnorm
      exact mem_normalizer_iff_conjSub_eq.mpr (AscQuot.conjSub_eq_of_normal _ x)
  have hYH : (⨆ J ∈ Ω, J : Subgroup G) ≤ H :=
    c.layer_le_H hEA hEM (h3 G Ω K S R W H c) hK'tw hK'ne hR' hR'K' hR'S hX hKX
      hK'X hgen hSY
  obtain ⟨u, huR, hu4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp hRR
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  have hle : conjSub g K ≤ ⨆ J ∈ Ω, J :=
    le_iSup₂_of_le (conjSub g K) (hΩ.conjInvariant g K c.stand.mem) le_rfl
  exact c.mem_of_conj_mem hEA hEM (hRK huR) hu4 (hYH (hle (conj_mem_conjSub (hRK huR))))

end CFSG.ClassicalInvolution.Asc77
