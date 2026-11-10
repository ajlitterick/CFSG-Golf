module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SolvableConstraint
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NonsolvableSections
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SectionTransport
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem normal_subgroup_primeComplementCore_le
    {G : Type*} [Group G] [Finite G] (prime : ℕ)
    (normalGroup : Subgroup G) (hnormal : normalGroup.Normal) :
    Subgroup.map normalGroup.subtype (primeComplementCore prime) ≤ primeComplementCore prime := by
  let : normalGroup.Normal := hnormal
  let : (primeComplementCore (G := normalGroup) prime).Characteristic :=
    primeComplementCore_characteristic prime
  have hmappedNormal : (Subgroup.map normalGroup.subtype (primeComplementCore prime)).Normal := by
    infer_instance
  exact normal_coprime_le_primeComplementCore prime _ hmappedNormal
    ((primeComplementCore_coprime prime).of_dvd_right
      ((primeComplementCore (G := normalGroup) prime).card_map_dvd normalGroup.subtype))

theorem normal_subgroup_pCore_le
    {G : Type*} [Group G] (prime : ℕ) (normalGroup : Subgroup G)
    (hnormal : normalGroup.Normal) :
    Subgroup.map normalGroup.subtype (pCore prime normalGroup) ≤ pCore prime G := by
  let : normalGroup.Normal := hnormal
  let : (pCore prime normalGroup).Characteristic := pCore_characteristic prime
  have hmappedNormal : (Subgroup.map normalGroup.subtype (pCore prime normalGroup)).Normal := by
    infer_instance
  exact normal_pGroup_le_pCore prime _ hmappedNormal ((pCore_isPGroup prime).map normalGroup.subtype)

theorem pCore_centralizer_internal_pCore_le_center
    {G : Type*} [Group G] (prime : ℕ) :
    pCore prime (Subgroup.centralizer (pCore prime G : Set G)) ≤
      Subgroup.center (Subgroup.centralizer (pCore prime G : Set G)) := by
  let centralizingGroup := Subgroup.centralizer (pCore prime G : Set G)
  have hnormal := centralizer_normal_of_normal _ (pCore_normal prime (G := G))
  have hcoreLe := normal_subgroup_pCore_le prime centralizingGroup hnormal
  intro coreElement hcoreElement
  apply Subgroup.mem_center_iff.mpr
  intro centralizingElement
  apply Subtype.ext
  have hambientCore : (coreElement : G) ∈ pCore prime G :=
    hcoreLe (Subgroup.mem_map_of_mem centralizingGroup.subtype hcoreElement)
  exact (Subgroup.mem_centralizer_iff.mp centralizingElement.property coreElement.val hambientCore).symm

theorem reduced_pCore_centralizer_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    primeComplementCore (G := Subgroup.centralizer
      (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))) prime = ⊥ := by
  let centralizingGroup := Subgroup.centralizer
    (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
  have hnormal := centralizer_normal_of_normal _ (pCore_normal prime (G := G ⧸ primeComplementCore prime))
  have hbound := normal_subgroup_primeComplementCore_le prime centralizingGroup hnormal
  rw [primeComplementCore_quotient_eq_bot] at hbound
  exact (Subgroup.map_eq_bot_iff_of_injective _ centralizingGroup.subtype_injective).mp
    (le_bot_iff.mp hbound)


end CFSG.RankThreeCoreUniqueness.Helpers
