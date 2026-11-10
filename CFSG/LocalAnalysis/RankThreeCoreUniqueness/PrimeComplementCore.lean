module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SignalizerBaer

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def primeComplementCore {G : Type*} [Group G] (prime : ℕ) : Subgroup G :=
  sSup {subgroup : Subgroup G | subgroup.Normal ∧ prime.Coprime (Nat.card subgroup)}

theorem normal_coprime_sup_coprime
    {G : Type*} [Group G] [Finite G] (prime : ℕ)
    (firstGroup secondGroup : Subgroup G) (hsecondNormal : secondGroup.Normal)
    (hfirst : prime.Coprime (Nat.card firstGroup))
    (hsecond : prime.Coprime (Nat.card secondGroup)) :
    prime.Coprime (Nat.card (firstGroup ⊔ secondGroup : Subgroup G)) := by
  let : secondGroup.Normal := hsecondNormal
  have hcard := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) secondGroup
    (firstGroup ⊔ secondGroup) bot_le le_sup_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Subgroup.relIndex_sup_right] at hcard
  rw [← hcard]
  exact hsecond.mul_right (hfirst.of_dvd_right (secondGroup.relIndex_dvd_card firstGroup))

instance primeComplementCore_normal
    {G : Type*} [Group G] (prime : ℕ) : (primeComplementCore (G := G) prime).Normal := by
  exact Subgroup.sSup_normal _ (fun _ hsubgroup => hsubgroup.1)

theorem normal_coprime_le_primeComplementCore
    {G : Type*} [Group G] (prime : ℕ) (subgroup : Subgroup G)
    (hnormal : subgroup.Normal) (hcoprime : prime.Coprime (Nat.card subgroup)) :
    subgroup ≤ primeComplementCore prime :=
  le_sSup ⟨hnormal, hcoprime⟩

theorem primeComplementCore_coprime
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    prime.Coprime (Nat.card (primeComplementCore (G := G) prime)) := by
  classical
  have hbottom : (⊥ : Subgroup G).Normal ∧ prime.Coprime (Nat.card (⊥ : Subgroup G)) :=
    ⟨by infer_instance, by
      rw [Subgroup.card_bot]
      exact Nat.coprime_one_right prime⟩
  obtain ⟨maximalGroup, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => subgroup.Normal ∧ prime.Coprime (Nat.card subgroup))
    hbottom
  have hcontains (subgroup : Subgroup G) (hnormal : subgroup.Normal)
      (hcoprime : prime.Coprime (Nat.card subgroup)) : subgroup ≤ maximalGroup := by
    let : subgroup.Normal := hnormal
    let : maximalGroup.Normal := hmaximal.prop.1
    have hsupProperty : (subgroup ⊔ maximalGroup : Subgroup G).Normal ∧
        prime.Coprime (Nat.card (subgroup ⊔ maximalGroup : Subgroup G)) :=
      ⟨by infer_instance, normal_coprime_sup_coprime prime subgroup maximalGroup
        hmaximal.prop.1 hcoprime hmaximal.prop.2⟩
    have hequal := hmaximal.eq_of_le hsupProperty le_sup_right
    exact le_sup_left.trans (le_of_eq hequal.symm)
  have hequal : primeComplementCore prime = maximalGroup := by
    apply le_antisymm
    · apply sSup_le
      rintro subgroup ⟨hnormal, hcoprime⟩
      exact hcontains subgroup hnormal hcoprime
    · exact normal_coprime_le_primeComplementCore prime maximalGroup
        hmaximal.prop.1 hmaximal.prop.2
  rw [hequal]
  exact hmaximal.prop.2

theorem primeComplementCore_characteristic
    {G : Type*} [Group G] (prime : ℕ) :
    (primeComplementCore (G := G) prime).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  rintro subgroup ⟨hnormal, hcoprime⟩
  apply Subgroup.map_le_iff_le_comap.mp
  exact normal_coprime_le_primeComplementCore prime (subgroup.map automorphism.toMonoidHom)
    (hnormal.map automorphism.toMonoidHom automorphism.surjective)
    (hcoprime.of_dvd_right (subgroup.card_map_dvd automorphism.toMonoidHom))

@[expose] def HasPrimeConstraint {G : Type*} [Group G] (prime : ℕ) : Prop :=
  ∃ normalGroup : Subgroup (G ⧸ primeComplementCore prime), normalGroup.Normal ∧
    IsPGroup prime normalGroup ∧ Subgroup.centralizer (normalGroup : Set _) ≤ normalGroup

theorem prime_constraint_signalizer_le_primeComplementCore
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hconstraint : HasPrimeConstraint (G := G) prime)
    (actingGroup signalizer : Subgroup G) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcontains : ∀ element : G,
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    signalizer ≤ primeComplementCore prime := by
  let : (primeComplementCore (G := G) prime).Normal := primeComplementCore_normal prime
  obtain ⟨normalGroup, hnormal, hpGroup, hcentralizer⟩ := hconstraint
  have hkernel : prime.Coprime
      (Nat.card (QuotientGroup.mk' (primeComplementCore (G := G) prime)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime prime
  have hbound := quotient_self_centralizing_core_signalizer_le_kernel prime hprime hodd
    (QuotientGroup.mk' (primeComplementCore (G := G) prime))
    (QuotientGroup.mk'_surjective _) hkernel normalGroup hnormal hpGroup hcentralizer
    actingGroup signalizer hactor hsignalizer hinvariant hcontains
  rwa [QuotientGroup.ker_mk'] at hbound

theorem ambient_prime_constraint_signalizer_le_core
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (overgroup actingGroup signalizer : Subgroup G)
    (hconstraint : HasPrimeConstraint (G := overgroup) prime)
    (hactor : IsPGroup prime actingGroup) (hactorLe : actingGroup ≤ overgroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer)) (hsignalizerLe : signalizer ≤ overgroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcontains : ∀ element : G, element ∈ overgroup →
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    signalizer ≤ (primeComplementCore (G := overgroup) prime).map overgroup.subtype := by
  have hactorInternal : IsPGroup prime (actingGroup.subgroupOf overgroup) :=
    hactor.of_equiv (Subgroup.subgroupOfEquivOfLe hactorLe).symm
  have hcoprimeInternal : prime.Coprime (Nat.card (signalizer.subgroupOf overgroup)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsignalizerLe).toEquiv]
    exact hsignalizer
  have hinvariantInternal : actingGroup.subgroupOf overgroup ≤
      Subgroup.normalizer (signalizer.subgroupOf overgroup : Set overgroup) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hsignalizerLe]
    exact Subgroup.comap_mono hinvariant
  have hcontainsInternal : ∀ element : overgroup,
      element ∈ Subgroup.centralizer (actingGroup.subgroupOf overgroup : Set overgroup) →
      orderOf element = prime → element ∈ actingGroup.subgroupOf overgroup := by
    intro element hcentralizes horder
    apply hcontains element element.property
    · apply Subgroup.mem_centralizer_iff.mpr
      intro actingElement hactingElement
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentralizes
        (⟨actingElement, hactorLe hactingElement⟩ : overgroup) hactingElement)
    · rwa [Subgroup.orderOf_coe]
  have hbound := prime_constraint_signalizer_le_primeComplementCore prime hprime hodd hconstraint
    (actingGroup.subgroupOf overgroup) (signalizer.subgroupOf overgroup) hactorInternal
    hcoprimeInternal hinvariantInternal hcontainsInternal
  have hmapped := Subgroup.map_mono (f := overgroup.subtype) hbound
  rwa [Subgroup.map_subgroupOf_eq_of_le hsignalizerLe] at hmapped


end CFSG.RankThreeCoreUniqueness.Helpers
