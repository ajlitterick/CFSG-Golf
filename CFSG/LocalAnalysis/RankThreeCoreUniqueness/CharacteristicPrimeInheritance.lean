module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralCoreReduction

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem self_centralizing_pCore_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcentralizer : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G) :
    primeComplementCore (G := G) prime = ⊥ := by
  let : (pCore prime G).Normal := pCore_normal prime
  have hdisjoint : Disjoint (primeComplementCore (G := G) prime) (pCore prime G) := by
    apply disjoint_iff.mpr
    have hcoprime : prime.Coprime
        (Nat.card ((primeComplementCore prime).subgroupOf (pCore prime G))) := by
      rw [← Subgroup.inf_subgroupOf_right (primeComplementCore prime) (pCore prime G),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : primeComplementCore (G := G) prime ⊓ pCore prime G ≤ pCore prime G)).toEquiv]
      exact (primeComplementCore_coprime prime).of_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)
    have hinf := coprime_subgroup_of_pGroup_eq_bot prime hprime
      (pCore_isPGroup prime) ((primeComplementCore prime).subgroupOf (pCore prime G))
      hcoprime
    have hmapped := congrArg (Subgroup.map (pCore prime G).subtype) hinf
    rw [← Subgroup.inf_subgroupOf_right (primeComplementCore prime) (pCore prime G),
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] at hmapped
    exact hmapped
  have hcommute := Subgroup.commutator_eq_bot_of_disjoint hdisjoint
  have hbound := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommute).trans hcentralizer
  apply le_bot_iff.mp
  exact (le_inf le_rfl hbound).trans (disjoint_iff.mp hdisjoint).le

theorem normal_subgroup_self_centralizing_pCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcentralizer : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (normalGroup : Subgroup G) (hnormal : normalGroup.Normal) :
    Subgroup.centralizer (pCore prime normalGroup : Set normalGroup) ≤ pCore prime normalGroup := by
  let : normalGroup.Normal := hnormal
  let : (pCore prime G).Normal := pCore_normal prime
  let : (pCore prime normalGroup).Characteristic := pCore_characteristic prime
  let internalCentralizer := Subgroup.centralizer (pCore prime normalGroup : Set normalGroup)
  let : internalCentralizer.Characteristic := by infer_instance
  let ambientCentralizer := Subgroup.map normalGroup.subtype internalCentralizer
  let : ambientCentralizer.Normal := by infer_instance
  have hcentralizerLe : ambientCentralizer ≤ normalGroup := Subgroup.map_subtype_le _
  have hcommute : ambientCentralizer ≤ Subgroup.centralizer (pCoreOf prime normalGroup : Set G) := by
    rintro element ⟨preimage, hpreimage, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro coreElement ⟨corePreimage, hcorePreimage, rfl⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hpreimage corePreimage hcorePreimage)
  have hinfLe : normalGroup ⊓ pCore prime G ≤ pCoreOf prime normalGroup :=
    normal_pGroup_le_pCoreOf prime _ normalGroup inf_le_left inferInstance
      ((pCore_isPGroup prime).to_le inf_le_right)
  have hcommutatorLe : ⁅ambientCentralizer, pCore prime G⁆ ≤ pCoreOf prime normalGroup :=
    (le_inf ((Subgroup.commutator_le_left _ _).trans hcentralizerLe)
      (Subgroup.commutator_le_right _ _)).trans hinfLe
  have hcentralizesFirst : ⁅⁅ambientCentralizer, pCore prime G⁆, ambientCentralizer⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono le_rfl hcommutatorLe).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcommute).le
  have hcentralizesSecond : ⁅⁅pCore prime G, ambientCentralizer⁆, ambientCentralizer⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm (pCore prime G) ambientCentralizer]
  have hderivedCentralizes : ⁅⁅ambientCentralizer, ambientCentralizer⁆, pCore prime G⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hcentralizesFirst hcentralizesSecond
  have hderivedCore : ⁅ambientCentralizer, ambientCentralizer⁆ ≤ pCoreOf prime normalGroup := by
    apply le_trans _ hinfLe
    exact le_inf ((Subgroup.commutator_le_self _).trans hcentralizerLe)
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hderivedCentralizes).trans hcentralizer)
  have hnilpotent : Group.IsNilpotent ambientCentralizer := by
    apply Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := 2)
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero, Subgroup.commutator_comm]
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono le_rfl hderivedCore).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcommute).le
  have hpGroup := normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot prime hprime
    (self_centralizing_pCore_primeComplementCore_eq_bot prime hprime hcentralizer)
    ambientCentralizer inferInstance hnilpotent
  have hbound := normal_pGroup_le_pCoreOf prime ambientCentralizer normalGroup hcentralizerLe
    inferInstance hpGroup
  intro element helement
  have hambient := hbound (Subgroup.mem_map_of_mem normalGroup.subtype helement)
  have hinternal : element ∈ (pCoreOf prime normalGroup).subgroupOf normalGroup := hambient
  rwa [pCoreOf_subgroupOf] at hinternal

theorem self_centralizing_pCore_of_mulEquiv
    {G Image : Type*} [Group G] [Group Image] (prime : ℕ) (equivalence : G ≃* Image)
    (hcentralizer : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G) :
    Subgroup.centralizer (pCore prime Image : Set Image) ≤ pCore prime Image := by
  intro element helement
  have hpreimageCentralizes : equivalence.symm element ∈
      Subgroup.centralizer (pCore prime G : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro coreElement hcoreElement
    have himageCore : equivalence coreElement ∈ pCore prime Image :=
      pCore_map_mulEquiv_le prime equivalence
        (Subgroup.mem_map_of_mem equivalence.toMonoidHom hcoreElement)
    apply equivalence.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      Subgroup.mem_centralizer_iff.mp helement (equivalence coreElement) himageCore
  have himage := pCore_map_mulEquiv_le prime equivalence
    (Subgroup.mem_map_of_mem equivalence.toMonoidHom (hcentralizer hpreimageCentralizes))
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using himage

theorem normal_subgroupOf_self_centralizing_pCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (subgroup overgroup : Subgroup G) (hbound : subgroup ≤ overgroup)
    (hnormal : (subgroup.subgroupOf overgroup).Normal)
    (hcentralizer : Subgroup.centralizer (pCore prime overgroup : Set overgroup) ≤
      pCore prime overgroup) :
    Subgroup.centralizer (pCore prime subgroup : Set subgroup) ≤ pCore prime subgroup :=
  self_centralizing_pCore_of_mulEquiv prime (Subgroup.subgroupOfEquivOfLe hbound)
    (normal_subgroup_self_centralizing_pCore prime hprime hcentralizer
      (subgroup.subgroupOf overgroup) hnormal)


theorem charTwo_twoLocal_internal_self_centralizing_core
    {G : Type*} [Group G] [Finite G] (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) :
    Subgroup.centralizer (pCore 2 localGroup : Set localGroup) ≤ pCore 2 localGroup := by
  intro element helement
  have hambient : element.val ∈ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro other ⟨preimage, hpreimage, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp helement preimage hpreimage)
  have hcore := hchar localGroup hlocal ⟨element.property, hambient⟩
  have hinternal : element ∈ (pCoreOf 2 localGroup).subgroupOf localGroup := hcore
  rwa [pCoreOf_subgroupOf] at hinternal


end CFSG.RankThreeCoreUniqueness.Helpers
