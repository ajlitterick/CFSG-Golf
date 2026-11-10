module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.InvolutionCentralizer

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem centralPrimeTorsion_rank_eq_center_rank
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) :
    pRank prime (centralPrimeTorsion prime source) = pRank prime (Subgroup.center source) := by
  apply le_antisymm
  · apply pRank_mono prime hprime
    intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).1
  · obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
      pRank_attained prime hprime (Subgroup.center source)
    apply le_csSup (pRank_bddAbove prime hprime _)
    refine ⟨elementary, ?_, helementary, hcard⟩
    intro member hmember
    exact (mem_centralPrimeTorsion prime member).mpr
      ⟨hcontained hmember, helementary.2 member hmember⟩

theorem noncyclic_commutative_pGroup_rank_at_least_two
    {source : Type u} [CommGroup source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hsource : IsPGroup prime source)
    (hnoncyclic : ¬ IsCyclic source) : 2 ≤ pRank prime (⊤ : Subgroup source) := by
  by_contra hsmall
  exact hnoncyclic (commutative_pGroup_isCyclic_of_rank_le_one prime hprime hsource (by omega))

theorem noncyclic_characteristic_abelian_pGroup_has_characteristic_elementary
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hsource : IsPGroup prime source)
    (abelian : Subgroup source) [abelian.Characteristic]
    (habelian : IsMulCommutative abelian) (hnoncyclic : ¬ IsCyclic abelian) :
    ∃ elementary : Subgroup source, elementary.Characteristic ∧
      elementary ≤ abelian ∧ IsElemAbelian prime elementary ∧ 2 ≤ pRank prime elementary := by
  let : IsMulCommutative abelian := habelian
  let : CommGroup abelian := IsMulCommutative.instCommGroup
  let torsion := centralPrimeTorsion prime abelian
  let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
  let elementary := torsion.map abelian.subtype
  have htorsionRank : 2 ≤ pRank prime torsion := by
    rw [centralPrimeTorsion_rank_eq_center_rank prime hprime,
      Subgroup.center_eq_top]
    exact noncyclic_commutative_pGroup_rank_at_least_two prime hprime
      (hsource.to_subgroup abelian) hnoncyclic
  refine ⟨elementary, inferInstance, Subgroup.map_subtype_le torsion,
    elementary_abelian_map prime (centralPrimeTorsion_elementary prime) abelian.subtype, ?_⟩
  rw [pRank_map_of_injective prime hprime abelian.subtype Subtype.val_injective]
  exact htorsionRank

theorem no_large_characteristic_elementary_forces_characteristic_abelian_cyclic
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hsource : IsPGroup prime source)
    (hsmall : ∀ elementary : Subgroup source, elementary.Characteristic →
      IsElemAbelian prime elementary → pRank prime elementary ≤ 1)
    (abelian : Subgroup source) [abelian.Characteristic]
    (habelian : IsMulCommutative abelian) : IsCyclic abelian := by
  by_contra hnoncyclic
  obtain ⟨elementary, hcharacteristic, _, helementary, hrank⟩ :=
    noncyclic_characteristic_abelian_pGroup_has_characteristic_elementary prime hprime hsource
      abelian habelian hnoncyclic
  have hbound := hsmall elementary hcharacteristic helementary
  omega


theorem escaping_primeCore_quotient_normal_pGroup_characteristic_abelian_isCyclic
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormal : IsPGroup prime normal)
    (abelian : Subgroup normal) [abelian.Characteristic]
    (habelian : IsMulCommutative abelian) : IsCyclic abelian := by
  apply no_large_characteristic_elementary_forces_characteristic_abelian_cyclic
    prime hprime hnormal _ abelian habelian
  intro elementary hcharacteristic helementary
  let : elementary.Characteristic := hcharacteristic
  let image := elementary.map normal.subtype
  let : image.Normal := inferInstance
  have himageElementary : IsElemAbelian prime image :=
    elementary_abelian_map prime helementary normal.subtype
  have hbound := escaping_rank_three_primeCore_quotient_normal_elementary_rank_le_one
    prime hprime sylow hsylow hcore hrank hescape image himageElementary
  rw [pRank_map_of_injective prime hprime normal.subtype Subtype.val_injective] at hbound
  exact hbound


end CFSG.PreuniquenessRankFour.Helpers
