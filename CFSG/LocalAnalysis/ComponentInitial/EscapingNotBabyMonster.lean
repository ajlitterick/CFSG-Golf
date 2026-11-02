module

public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.Monster.B.Final.PinnedBOrder
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial in
theorem commuting_block_baby_monster_overgroup_exclusion {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.B) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hinv : ∀ K ∈ block J, ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 := by
    intro K hK
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K) 2
      (even_iff_two_dvd.1 (hπKq K hK).2)
    obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
      (by rw [Subgroup.orderOf_coe, hu])
    exact ⟨t, htK, ht2⟩
  have h17 : ∀ Ka ∈ block J, ∀ Kb ∈ block J, Ka ≠ Kb →
      17 ∣ Nat.card (centerQuotientImage L Ka ⧸ center (centerQuotientImage L Ka)) := by
    intro Ka hKa Kb hKb hab
    obtain ⟨t, htK, ht2⟩ := hinv Kb hKb
    obtain ⟨hπt, hcompK⟩ := hloc Ka hKa Kb hKb hab t htK ht2
    have hB := (isComponentOf_iff_isComponent_subgroupOf hcompK.1).1 hcompK
    have h :=
      (Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ _
        hπt _ hB).2.2
    let φ := Subgroup.subgroupOfEquivOfLe hcompK.1
    rwa [(Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv)] at h
  have hmul := card_quotient_center_mul_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
    (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L))
  rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr e.toEquiv,
    Monster.B.pinned_B_explicit_native_isomorphism_simplicity_and_order.2.2.2.2] at hmul
  have h289 := (Nat.mul_dvd_mul (h17 K₁ hK₁ K₂ hK₂ hne) (h17 K₂ hK₂ K₁ hK₁ hne.symm)).trans hmul
  norm_num at h289

end CFSG.LocalAnalysis.ComponentInitial
