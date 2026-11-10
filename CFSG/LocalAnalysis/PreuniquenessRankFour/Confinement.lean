module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.HyperplaneGeneration
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open
open CFSG.Open
open scoped Pointwise

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem elementary_abelian_map
    {source : Type u} {target : Type v} [Group source] [Group target]
    (prime : ℕ) {elementary : Subgroup source}
    (helementary : IsElemAbelian prime elementary) (hom : source →* target) :
    IsElemAbelian prime (elementary.map hom) := CFSG.Open.IsElemAbelian.map helementary _

theorem exists_conjugate_le_sylow_of_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] (sylow : Sylow prime ambient)
    {overgroup subgroup : Subgroup ambient} (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hsubgroup : subgroup ≤ overgroup) (hgroup : IsPGroup prime subgroup) :
    ∃ conjugator : overgroup,
      subgroup.map (MulAut.conj (conjugator : ambient)).toMonoidHom ≤ sylow := by
  have hsubgroupP : IsPGroup prime (subgroup.subgroupOf overgroup) :=
    hgroup.comap_subtype
  obtain ⟨containedSylow, hcontained⟩ := hsubgroupP.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ :=
    MulAction.exists_smul_eq overgroup containedSylow (sylow.subtype hsylow)
  refine ⟨conjugator, ?_⟩
  intro element helement
  obtain ⟨lift, hlift, rfl⟩ := helement
  let sourceElement : overgroup := ⟨lift, hsubgroup hlift⟩
  have hsource : sourceElement ∈ containedSylow := hcontained hlift
  have hconjugate : conjugator * sourceElement * conjugator⁻¹ ∈
      ((conjugator • containedSylow : Sylow prime overgroup) : Set overgroup) := by
    rw [@Sylow.coe_smul prime overgroup _ conjugator containedSylow]
    exact ⟨sourceElement, hsource, rfl⟩
  rw [hconjugator] at hconjugate
  exact hconjugate

theorem twoSubgroup_le_of_elementary_in_containing_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylow : Sylow prime ambient) {overgroup elementary twoGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (hcontained : elementary ≤ overgroup) (htwo : IsPGroup 2 twoGroup)
    (hnormalized : elementary ≤ Subgroup.normalizer (twoGroup : Set ambient)) :
    twoGroup ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hgroup : IsPGroup prime elementary := IsPGroup.of_card hcard
  obtain ⟨conjugator, hconjugator⟩ := exists_conjugate_le_sylow_of_le prime sylow
    hsylow hcontained hgroup
  let equivalence := MulAut.conj (conjugator : ambient)
  have hnormalizedMap : elementary.map equivalence.toMonoidHom ≤
      Subgroup.normalizer (twoGroup.map equivalence.toMonoidHom : Set ambient) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hnormalized
  have htwoMap : twoGroup.map equivalence.toMonoidHom ≤ overgroup :=
    (elementary_normalized_twoSubgroup_le_weakCore prime hprime hodd
      (elementary_abelian_map prime helementary equivalence.toMonoidHom) rank hrank
      (by rw [Subgroup.card_map_of_injective equivalence.injective, hcard])
      hconjugator (htwo.map equivalence.toMonoidHom) hnormalizedMap).trans hcore
  intro element helement
  have hconjugate := htwoMap (Subgroup.mem_map_of_mem equivalence.toMonoidHom helement)
  have hnormalizes : (conjugator : ambient) ∈
      Subgroup.normalizer (overgroup : Set ambient) :=
    Subgroup.le_normalizer conjugator.property
  exact (Subgroup.mem_normalizer_iff.mp hnormalizes element).mpr hconjugate

theorem intersecting_local_twoCore_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylow : Sylow prime ambient) {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup)) :
    pCoreOf 2 localGroup ≤ overgroup := by
  obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
    pRank_attained prime hprime (localGroup ⊓ overgroup)
  exact twoSubgroup_le_of_elementary_in_containing_sylow prime hprime hodd sylow
    hsylow hcore helementary (pRank prime (localGroup ⊓ overgroup)) hrank hcard
    (hcontained.trans inf_le_right) (pCoreOf_isPGroup 2 localGroup)
    ((hcontained.trans inf_le_left).trans (subgroup_normalizes_pCoreOf 2 localGroup))

theorem normalizer_le_of_rank_in_containing_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup subgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsubgroup : subgroup ≤ overgroup) (hgroup : IsPGroup prime subgroup)
    (hrank : 3 ≤ pRank prime subgroup) :
    Subgroup.normalizer (subgroup : Set ambient) ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨conjugator, hconjugator⟩ := exists_conjugate_le_sylow_of_le prime sylow
    hsylow hsubgroup hgroup
  let equivalence := MulAut.conj (conjugator : ambient)
  obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
    pRank_attained prime hprime subgroup
  have hrankMap : 3 ≤ pRank prime (subgroup.map equivalence.toMonoidHom) := by
    apply hrank.trans
    apply le_csSup (pRank_bddAbove prime hprime (subgroup.map equivalence.toMonoidHom))
    refine ⟨elementary.map equivalence.toMonoidHom, Subgroup.map_mono hcontained,
      elementary_abelian_map prime helementary equivalence.toMonoidHom, ?_⟩
    rw [Subgroup.card_map_of_injective equivalence.injective, hcard]
  have hnormalizerMap :
      (Subgroup.normalizer (subgroup : Set ambient)).map equivalence.toMonoidHom ≤
        overgroup := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact (normalizer_le_weakCore_of_rank prime hprime
      (subgroup.map equivalence.toMonoidHom) hrankMap).trans
        ((weakCore_mono prime hprime hconjugator).trans hcore)
  intro element helement
  have hconjugate := hnormalizerMap
    (Subgroup.mem_map_of_mem equivalence.toMonoidHom helement)
  exact (Subgroup.mem_normalizer_iff.mp
    (Subgroup.le_normalizer conjugator.property) element).mpr hconjugate

theorem intersecting_pSubgroup_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup subgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hgroup : IsPGroup prime subgroup)
    (hrank : 3 ≤ pRank prime (subgroup ⊓ overgroup)) :
    subgroup ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent subgroup := hgroup.isNilpotent
  have hnormalizer :
      Subgroup.normalizer ((subgroup ⊓ overgroup).subgroupOf subgroup : Set subgroup) =
        (subgroup ⊓ overgroup).subgroupOf subgroup := by
    apply le_antisymm _ Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq inf_le_left]
    intro element helement
    exact ⟨element.property,
      normalizer_le_of_rank_in_containing_sylow prime hprime sylow hsylow hcore
        inf_le_right (hgroup.to_le inf_le_left) hrank helement⟩
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := subgroup)))
      ((subgroup ⊓ overgroup).subgroupOf subgroup) hnormalizer
  exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

theorem exists_normalized_sylow_of_pGroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (actingPrime sylowPrime : ℕ) [Fact actingPrime.Prime] [Fact sylowPrime.Prime]
    {acting source : Subgroup ambient} (hacting : IsPGroup actingPrime acting)
    (hcard : ¬ actingPrime ∣ Nat.card (Sylow sylowPrime source))
    (hnormalized : acting ≤ Subgroup.normalizer (source : Set ambient)) :
    ∃ sylow : Sylow sylowPrime source,
      acting ≤ Subgroup.normalizer
        ((sylow : Subgroup source).map source.subtype : Set ambient) := by
  let actionHom : acting →* MulAut source :=
    source.normalizerMonoidHom.comp (Subgroup.inclusion hnormalized)
  let : MulDistribMulAction acting source :=
    MulDistribMulAction.compHom source actionHom
  obtain ⟨sylow, hfixed⟩ :=
    hacting.nonempty_fixed_point_of_prime_not_dvd_card (Sylow sylowPrime source) hcard
  refine ⟨sylow, Subgroup.le_normalizer_iff.mpr ?_⟩
  intro scalar hscalar element helement
  obtain ⟨lift, hlift, rfl⟩ := helement
  let actingScalar : acting := ⟨scalar, hscalar⟩
  have hmap : actingScalar • (sylow : Subgroup source) = (sylow : Subgroup source) := by
    rw [← Sylow.pointwise_smul_def, hfixed actingScalar]
  have hsmul : actingScalar • lift ∈ (sylow : Subgroup source) := by
    rw [← hmap, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map_of_mem _ hlift
  refine Subgroup.mem_map.mpr ⟨actingScalar • lift, hsmul, ?_⟩
  exact source.normalizerMonoidHom_apply_apply_coe
    ⟨scalar, hnormalized hscalar⟩ lift

theorem exists_normalized_same_prime_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime]
    {acting source : Subgroup ambient} (hacting : IsPGroup prime acting)
    (hnormalized : acting ≤ Subgroup.normalizer (source : Set ambient)) :
    ∃ sylow : Sylow prime source,
      acting ≤ Subgroup.normalizer
        ((sylow : Subgroup source).map source.subtype : Set ambient) := by
  exact exists_normalized_sylow_of_pGroup prime prime hacting
    (not_dvd_card_sylow prime source) hnormalized

theorem exists_normalized_sylow_of_coprime_pGroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (actingPrime sylowPrime : ℕ) [Fact actingPrime.Prime] [Fact sylowPrime.Prime]
    {acting source : Subgroup ambient} (hacting : IsPGroup actingPrime acting)
    (hcoprime : ¬ actingPrime ∣ Nat.card source)
    (hnormalized : acting ≤ Subgroup.normalizer (source : Set ambient)) :
    ∃ sylow : Sylow sylowPrime source,
      acting ≤ Subgroup.normalizer
        ((sylow : Subgroup source).map source.subtype : Set ambient) := by
  have hcard : ¬ actingPrime ∣ Nat.card (Sylow sylowPrime source) := by
    intro hdivides
    let sylow : Sylow sylowPrime source := Classical.choice inferInstance
    exact hcoprime (hdivides.trans
      (sylow.card_dvd_index.trans (sylow : Subgroup source).index_dvd_card))
  exact exists_normalized_sylow_of_pGroup actingPrime sylowPrime hacting hcard hnormalized

theorem coprime_subgroup_le_of_elementary_in_containing_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup elementary source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (hcontained : elementary ≤ overgroup) (hcoprime : ¬ prime ∣ Nat.card source)
    (hnormalized : elementary ≤ Subgroup.normalizer (source : Set ambient)) :
    source ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hacting : IsPGroup prime elementary := IsPGroup.of_card hcard
  have hnormalizedSylows : ∀ otherPrime : ℕ, otherPrime.Prime →
      ∃ otherSylow : Sylow otherPrime source,
        (otherSylow : Subgroup source).map source.subtype ≤ overgroup := by
    intro otherPrime hotherPrime
    let : Fact otherPrime.Prime := ⟨hotherPrime⟩
    obtain ⟨otherSylow, hnormalizedSylow⟩ :=
      exists_normalized_sylow_of_coprime_pGroup prime otherPrime hacting
        hcoprime hnormalized
    let otherGroup := (otherSylow : Subgroup source).map source.subtype
    obtain ⟨conjugator, hconjugator⟩ := exists_conjugate_le_sylow_of_le prime sylow
      hsylow hcontained hacting
    let equivalence := MulAut.conj (conjugator : ambient)
    let : CommGroup elementary := by
      let : IsMulCommutative elementary := helementary.1
      exact IsMulCommutative.instCommGroup
    let conjugatedElementary := elementary.map equivalence.toMonoidHom
    let conjugatedGroup := otherGroup.map equivalence.toMonoidHom
    have hnormalizedMap : conjugatedElementary ≤
        Subgroup.normalizer (conjugatedGroup : Set ambient) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hnormalizedSylow
    have helementaryMap := elementary_abelian_map prime helementary equivalence.toMonoidHom
    have hotherGroup : IsPGroup otherPrime conjugatedGroup :=
      (otherSylow.isPGroup'.map source.subtype).map equivalence.toMonoidHom
    have hconjugatedContained : conjugatedGroup ≤ overgroup := by
      by_cases hequal : prime = otherPrime
      · have hcardOne : Nat.card (otherSylow : Subgroup source) = 1 := by
          rcases otherSylow.isPGroup'.card_eq_or_dvd with hcardOne | hdivides
          · exact hcardOne
          · exact False.elim (hcoprime (hequal ▸
              hdivides.trans (otherSylow : Subgroup source).card_subgroup_dvd_card))
        have hotherBot := Subgroup.card_eq_one.mp hcardOne
        simp only [conjugatedGroup, otherGroup, hotherBot, Subgroup.map_bot]
        exact bot_le
      · exact (elementary_normalized_primeSubgroup_le_weakCore prime otherPrime
          hprime hotherPrime hequal helementaryMap rank hrank
          (by rw [Subgroup.card_map_of_injective equivalence.injective, hcard])
          hconjugator hotherGroup hnormalizedMap).trans hcore
    refine ⟨otherSylow, ?_⟩
    intro element helement
    have hconjugate := hconjugatedContained
      (Subgroup.mem_map_of_mem equivalence.toMonoidHom helement)
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer conjugator.property) element).mpr hconjugate
  have hindex : (overgroup.subgroupOf source).index = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro otherPrime hotherPrime
    let : Fact otherPrime.Prime := ⟨hotherPrime⟩
    obtain ⟨otherSylow, hcontainedSylow⟩ := hnormalizedSylows otherPrime hotherPrime
    have hcontainedSource : (otherSylow : Subgroup source) ≤ overgroup.subgroupOf source := by
      intro element helement
      exact hcontainedSylow (Subgroup.mem_map_of_mem source.subtype helement)
    intro hdivides
    exact otherSylow.not_dvd_index
      (hdivides.trans (Subgroup.index_dvd_of_le hcontainedSource))
  exact Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hindex)

theorem intersecting_local_primeCore_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup)) :
    GLBPrimeCore prime localGroup ≤ overgroup := by
  obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
    pRank_attained prime hprime (localGroup ⊓ overgroup)
  apply sSup_le
  rintro source ⟨hsource, hnormal, hcoprime⟩
  exact coprime_subgroup_le_of_elementary_in_containing_sylow prime hprime sylow
    hsylow hcore helementary (pRank prime (localGroup ⊓ overgroup)) hrank hcard
    (hcontained.trans inf_le_right)
    ((Nat.Prime.coprime_iff_not_dvd hprime).mp hcoprime)
    ((hcontained.trans inf_le_left).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hsource).mp hnormal))


theorem normal_subgroup_sylow_rank_forces_containment
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (normalGroup : Subgroup localGroup) [normalGroup.Normal]
    (hcontained : normalGroup.map localGroup.subtype ≤ overgroup)
    (hrank : 3 ≤ pRank prime (normalGroup.map localGroup.subtype)) :
    localGroup ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
    pRank_attained prime hprime (normalGroup.map localGroup.subtype)
  have hinside : elementary ≤ localGroup :=
    helementaryContained.trans (Subgroup.map_subtype_le normalGroup)
  have hsubgroup : elementary.subgroupOf localGroup ≤ normalGroup := by
    intro element helement
    obtain ⟨lift, hlift, hequal⟩ := helementaryContained helement
    have hequalSubtype : lift = element := Subtype.ext hequal
    exact hequalSubtype ▸ hlift
  have hgroup : IsPGroup prime (elementary.subgroupOf localGroup) :=
    (IsPGroup.of_card hcard).comap_subtype
  have hgroupInNormal : IsPGroup prime
      ((elementary.subgroupOf localGroup).subgroupOf normalGroup) := hgroup.comap_subtype
  obtain ⟨normalSylow, hnormalSylow⟩ := hgroupInNormal.exists_le_sylow
  let liftedSylow := (normalSylow : Subgroup normalGroup).map normalGroup.subtype
  have helementarySylow : elementary.subgroupOf localGroup ≤ liftedSylow := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hsubgroup]
    exact Subgroup.map_mono hnormalSylow
  have hliftedContained : liftedSylow.map localGroup.subtype ≤ overgroup :=
    (Subgroup.map_mono (Subgroup.map_subtype_le (normalSylow : Subgroup normalGroup))).trans
      hcontained
  have helementaryAmbient : elementary ≤ liftedSylow.map localGroup.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hinside]
    exact Subgroup.map_mono helementarySylow
  have hliftedRank : 3 ≤ pRank prime (liftedSylow.map localGroup.subtype) := by
    apply hrank.trans
    exact le_csSup (pRank_bddAbove prime hprime (liftedSylow.map localGroup.subtype))
      ⟨elementary, helementaryAmbient, helementary, hcard⟩
  have hnormalizer : Subgroup.normalizer
      (liftedSylow.map localGroup.subtype : Set ambient) ≤ overgroup :=
    normalizer_le_of_rank_in_containing_sylow prime hprime sylow hsylow hcore
      hliftedContained ((normalSylow.isPGroup'.map normalGroup.subtype).map
        localGroup.subtype) hliftedRank
  have hnormalizerInLocal : Subgroup.normalizer (liftedSylow : Set localGroup) ≤
      overgroup.subgroupOf localGroup := by
    have hsubgroupOf : (liftedSylow.map localGroup.subtype).subgroupOf localGroup =
        liftedSylow := Subgroup.comap_map_eq_self_of_injective
          (Subtype.val_injective) liftedSylow
    rw [← hsubgroupOf, ← Subgroup.subgroupOf_normalizer_eq
      (Subgroup.map_subtype_le liftedSylow)]
    intro element helement
    exact hnormalizer helement
  have htop : (⊤ : Subgroup localGroup) ≤ overgroup.subgroupOf localGroup := by
    rw [← normalSylow.normalizer_sup_eq_top]
    exact sup_le hnormalizerInLocal (Subgroup.map_le_iff_le_comap.mp hcontained)
  exact Subgroup.subgroupOf_eq_top.mp (top_unique htop)

theorem normalizer_le_of_subgroup_rank_in_containing_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup subgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hcontained : subgroup ≤ overgroup) (hrank : 3 ≤ pRank prime subgroup) :
    Subgroup.normalizer (subgroup : Set ambient) ≤ overgroup := by
  let localGroup := Subgroup.normalizer (subgroup : Set ambient)
  let normalGroup := subgroup.subgroupOf localGroup
  have hmap : normalGroup.map localGroup.subtype = subgroup :=
    Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer
  apply normal_subgroup_sylow_rank_forces_containment prime hprime sylow
    hsylow hcore normalGroup
  · rw [hmap]
    exact hcontained
  · rw [hmap]
    exact hrank

theorem normalizer_le_of_centralizer_rank_in_containing_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup subgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hcontained : subgroup ≤ overgroup) (hgroup : IsPGroup prime subgroup)
    (hrank : 2 ≤ pRank prime subgroup)
    (hcentralRank : 3 ≤ pRank prime
      (overgroup ⊓ Subgroup.centralizer (subgroup : Set ambient))) :
    Subgroup.normalizer (subgroup : Set ambient) ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
    pRank_attained prime hprime (overgroup ⊓ Subgroup.centralizer (subgroup : Set ambient))
  have hnormalized : elementary ≤ Subgroup.normalizer (subgroup : Set ambient) :=
    (helementaryContained.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hjoinGroup : IsPGroup prime (subgroup ⊔ elementary : Subgroup ambient) :=
    IsPGroup.to_sup_of_normal_left' hgroup (IsPGroup.of_card hcard) hnormalized
  obtain ⟨conjugator, hconjugator⟩ := exists_conjugate_le_sylow_of_le prime sylow
    hsylow (sup_le hcontained (helementaryContained.trans inf_le_left)) hjoinGroup
  let equivalence := MulAut.conj (conjugator : ambient)
  have hsubgroupMap : subgroup.map equivalence.toMonoidHom ≤ sylow :=
    (Subgroup.map_mono le_sup_left).trans hconjugator
  have helementaryMap : elementary.map equivalence.toMonoidHom ≤ sylow :=
    (Subgroup.map_mono le_sup_right).trans hconjugator
  have hcentralMap : elementary.map equivalence.toMonoidHom ≤
      Subgroup.centralizer (subgroup.map equivalence.toMonoidHom : Set ambient) := by
    intro element helement
    obtain ⟨lift, hlift, rfl⟩ := helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨otherLift, hotherLift, rfl⟩ := hother
    have hcomm := Subgroup.mem_centralizer_iff.mp
      ((helementaryContained.trans inf_le_right) hlift) otherLift hotherLift
    exact map_mul equivalence otherLift lift |>.symm.trans
      ((congrArg equivalence hcomm).trans (map_mul equivalence lift otherLift))
  have hcentralJoinRank : 3 ≤ pRank prime
      (subgroup.map equivalence.toMonoidHom ⊔
        ((sylow : Subgroup ambient) ⊓
          Subgroup.centralizer (subgroup.map equivalence.toMonoidHom : Set ambient))) := by
    apply hcentralRank.trans
    exact le_csSup (pRank_bddAbove prime hprime _)
      ⟨elementary.map equivalence.toMonoidHom,
        (le_inf helementaryMap hcentralMap).trans le_sup_right,
        elementary_abelian_map prime helementary equivalence.toMonoidHom,
        by rw [Subgroup.card_map_of_injective equivalence.injective, hcard]⟩
  have hsubgroupRank : 2 ≤ pRank prime (subgroup.map equivalence.toMonoidHom) := by
    obtain ⟨witness, hwitness, hwitnessElementary, hwitnessCard⟩ :=
      pRank_attained prime hprime subgroup
    apply hrank.trans
    exact le_csSup (pRank_bddAbove prime hprime _)
      ⟨witness.map equivalence.toMonoidHom, Subgroup.map_mono hwitness,
        elementary_abelian_map prime hwitnessElementary equivalence.toMonoidHom,
        by rw [Subgroup.card_map_of_injective equivalence.injective, hwitnessCard]⟩
  have hnormalizer : (Subgroup.normalizer (subgroup : Set ambient)).map
      equivalence.toMonoidHom ≤ overgroup := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact (normalizer_le_weakCore prime hsubgroupMap hsubgroupRank hcentralJoinRank).trans hcore
  intro element helement
  have hconjugate := hnormalizer (Subgroup.mem_map_of_mem equivalence.toMonoidHom helement)
  exact (Subgroup.mem_normalizer_iff.mp
    (Subgroup.le_normalizer conjugator.property) element).mpr hconjugate

theorem normal_subgroup_centralizer_rank_forces_containment
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (normalGroup : Subgroup localGroup) [normalGroup.Normal]
    (hcontained : normalGroup.map localGroup.subtype ≤ overgroup)
    (hrank : 2 ≤ pRank prime (normalGroup.map localGroup.subtype))
    (hcentralRank : 3 ≤ pRank prime (overgroup ⊓
      Subgroup.centralizer (normalGroup.map localGroup.subtype : Set ambient))) :
    localGroup ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
    pRank_attained prime hprime (normalGroup.map localGroup.subtype)
  have hinside : elementary ≤ localGroup :=
    helementaryContained.trans (Subgroup.map_subtype_le normalGroup)
  have hsubgroup : elementary.subgroupOf localGroup ≤ normalGroup := by
    intro element helement
    obtain ⟨lift, hlift, hequal⟩ := helementaryContained helement
    exact (Subtype.ext hequal : lift = element) ▸ hlift
  have hgroup : IsPGroup prime (elementary.subgroupOf localGroup) :=
    (IsPGroup.of_card hcard).comap_subtype
  have hgroupInNormal : IsPGroup prime
      ((elementary.subgroupOf localGroup).subgroupOf normalGroup) := hgroup.comap_subtype
  obtain ⟨normalSylow, hnormalSylow⟩ := hgroupInNormal.exists_le_sylow
  let liftedSylow := (normalSylow : Subgroup normalGroup).map normalGroup.subtype
  have helementarySylow : elementary.subgroupOf localGroup ≤ liftedSylow := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hsubgroup]
    exact Subgroup.map_mono hnormalSylow
  have hliftedNormal : liftedSylow.map localGroup.subtype ≤ normalGroup.map localGroup.subtype :=
    Subgroup.map_mono (Subgroup.map_subtype_le (normalSylow : Subgroup normalGroup))
  have helementaryAmbient : elementary ≤ liftedSylow.map localGroup.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hinside]
    exact Subgroup.map_mono helementarySylow
  have hliftedRank : 2 ≤ pRank prime (liftedSylow.map localGroup.subtype) := by
    apply hrank.trans
    exact le_csSup (pRank_bddAbove prime hprime _)
      ⟨elementary, helementaryAmbient, helementary, hcard⟩
  have hliftedCentralRank : 3 ≤ pRank prime (overgroup ⊓
      Subgroup.centralizer (liftedSylow.map localGroup.subtype : Set ambient)) :=
    hcentralRank.trans (pRank_mono prime hprime
      (inf_le_inf_left overgroup (Subgroup.centralizer_le hliftedNormal)))
  have hnormalizer : Subgroup.normalizer
      (liftedSylow.map localGroup.subtype : Set ambient) ≤ overgroup :=
    normalizer_le_of_centralizer_rank_in_containing_sylow prime hprime sylow hsylow hcore
      (hliftedNormal.trans hcontained)
      ((normalSylow.isPGroup'.map normalGroup.subtype).map localGroup.subtype)
      hliftedRank hliftedCentralRank
  have hnormalizerInLocal : Subgroup.normalizer (liftedSylow : Set localGroup) ≤
      overgroup.subgroupOf localGroup := by
    have hsubgroupOf : (liftedSylow.map localGroup.subtype).subgroupOf localGroup =
        liftedSylow := Subgroup.comap_map_eq_self_of_injective Subtype.val_injective liftedSylow
    rw [← hsubgroupOf, ← Subgroup.subgroupOf_normalizer_eq
      (Subgroup.map_subtype_le liftedSylow)]
    intro element helement
    exact hnormalizer helement
  have htop : (⊤ : Subgroup localGroup) ≤ overgroup.subgroupOf localGroup := by
    rw [← normalSylow.normalizer_sup_eq_top]
    exact sup_le hnormalizerInLocal (Subgroup.map_le_iff_le_comap.mp hcontained)
  exact Subgroup.subgroupOf_eq_top.mp (top_unique htop)

theorem normalizer_le_of_subgroup_and_centralizer_rank
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup subgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hcontained : subgroup ≤ overgroup) (hrank : 2 ≤ pRank prime subgroup)
    (hcentralRank : 3 ≤ pRank prime
      (overgroup ⊓ Subgroup.centralizer (subgroup : Set ambient))) :
    Subgroup.normalizer (subgroup : Set ambient) ≤ overgroup := by
  let localGroup := Subgroup.normalizer (subgroup : Set ambient)
  have hmap : (subgroup.subgroupOf localGroup).map localGroup.subtype = subgroup :=
    Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer
  apply normal_subgroup_centralizer_rank_forces_containment prime hprime sylow hsylow hcore
    (subgroup.subgroupOf localGroup)
  · rw [hmap]
    exact hcontained
  · rw [hmap]
    exact hrank
  · rw [hmap]
    exact hcentralRank


theorem intersecting_local_has_contained_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup)) :
    ∃ localSylow : Sylow prime localGroup,
      (localSylow : Subgroup localGroup).map localGroup.subtype ≤ overgroup ∧
      3 ≤ pRank prime ((localSylow : Subgroup localGroup).map localGroup.subtype) ∧
      Subgroup.normalizer
        ((localSylow : Subgroup localGroup).map localGroup.subtype : Set ambient) ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
    pRank_attained prime hprime (localGroup ⊓ overgroup)
  have hinside : elementary ≤ localGroup := helementaryContained.trans inf_le_left
  have hgroup : IsPGroup prime (elementary.subgroupOf localGroup) :=
    (IsPGroup.of_card hcard).comap_subtype
  obtain ⟨localSylow, hlocalSylow⟩ := hgroup.exists_le_sylow
  have helementarySylow : elementary ≤
      (localSylow : Subgroup localGroup).map localGroup.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hinside]
    exact Subgroup.map_mono hlocalSylow
  have hintersectionRank : 3 ≤ pRank prime
      ((localSylow : Subgroup localGroup).map localGroup.subtype ⊓ overgroup) := by
    apply hrank.trans
    exact le_csSup (pRank_bddAbove prime hprime _)
      ⟨elementary, le_inf helementarySylow
        (helementaryContained.trans inf_le_right), helementary, hcard⟩
  have hcontained := intersecting_pSubgroup_le prime hprime sylow hsylow hcore
    (localSylow.isPGroup'.map localGroup.subtype) hintersectionRank
  have hlocalRank : 3 ≤ pRank prime
      ((localSylow : Subgroup localGroup).map localGroup.subtype) :=
    hintersectionRank.trans (pRank_mono prime hprime inf_le_left)
  exact ⟨localSylow, hcontained, hlocalRank,
    normalizer_le_of_rank_in_containing_sylow prime hprime sylow hsylow hcore
      hcontained (localSylow.isPGroup'.map localGroup.subtype) hlocalRank⟩


theorem conjugated_sylow_le_iff_mem_of_normalizer_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] (sylow : Sylow prime ambient)
    {overgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hnormalizer : Subgroup.normalizer (sylow : Set ambient) ≤ overgroup)
    (conjugator : ambient) :
    ((conjugator • sylow : Sylow prime ambient) : Subgroup ambient) ≤ overgroup ↔
      conjugator ∈ overgroup := by
  constructor
  · intro hcontained
    obtain ⟨adjustment, hadjustment⟩ := exists_conjugate_le_sylow_of_le prime sylow
      hsylow hcontained (conjugator • sylow).isPGroup'
    have hmap : ((conjugator • sylow : Sylow prime ambient) : Subgroup ambient).map
        (MulAut.conj (adjustment : ambient)).toMonoidHom =
        (((adjustment : ambient) * conjugator) • sylow : Sylow prime ambient) := by
      rw [@Sylow.coe_subgroup_smul prime ambient _ conjugator sylow,
        @Sylow.coe_subgroup_smul prime ambient _ ((adjustment : ambient) * conjugator) sylow,
        Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
      change ((sylow : Subgroup ambient).map
        (MulAut.conj conjugator).toMonoidHom).map
        (MulAut.conj (adjustment : ambient)).toMonoidHom =
        (sylow : Subgroup ambient).map
          (MulAut.conj ((adjustment : ambient) * conjugator)).toMonoidHom
      rw [Subgroup.map_map]
      congr 1
      ext element
      change (adjustment : ambient) * (conjugator * element * conjugator⁻¹) *
        (adjustment : ambient)⁻¹ = ((adjustment : ambient) * conjugator) * element *
          ((adjustment : ambient) * conjugator)⁻¹
      group
    rw [hmap] at hadjustment
    have hequal : ((adjustment : ambient) * conjugator) • sylow = sylow :=
      Sylow.ext ((((adjustment : ambient) * conjugator) • sylow).is_maximal'
        sylow.isPGroup' hadjustment).symm
    have hproduct : (adjustment : ambient) * conjugator ∈ overgroup :=
      hnormalizer (Sylow.smul_eq_iff_mem_normalizer.mp hequal)
    simpa only [inv_mul_cancel_left] using
      overgroup.mul_mem (overgroup.inv_mem adjustment.property) hproduct
  · intro hcontained
    exact Sylow.smul_le hsylow (⟨conjugator, hcontained⟩ : overgroup)


theorem escaping_conjugate_overgroup_intersection_rank_le_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (conjugator : ambient) (hescape : conjugator ∉ overgroup) :
    pRank prime (overgroup.map (MulAut.conj conjugator).toMonoidHom ⊓ overgroup) ≤ 2 := by
  let : Fact prime.Prime := ⟨hprime⟩
  let conjugate := overgroup.map (MulAut.conj conjugator).toMonoidHom
  have hconjugatedSylow : ((conjugator • sylow : Sylow prime ambient) :
      Subgroup ambient) ≤ conjugate := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change (sylow : Subgroup ambient).map (MulAut.conj conjugator).toMonoidHom ≤ conjugate
    exact Subgroup.map_mono hsylow
  by_contra hlarge
  have hlocalRank : 3 ≤ pRank prime (conjugate ⊓ overgroup) := by
    change 3 ≤ pRank prime
      (overgroup.map (MulAut.conj conjugator).toMonoidHom ⊓ overgroup)
    omega
  obtain ⟨localSylow, hcontained, _, _⟩ := intersecting_local_has_contained_sylow
    prime hprime sylow hsylow hcore hlocalRank
  obtain ⟨adjustment, hadjustment⟩ := MulAction.exists_smul_eq conjugate
    ((conjugator • sylow).subtype hconjugatedSylow) localSylow
  have hsubtype : (((adjustment : ambient) • (conjugator • sylow) : Sylow prime ambient).subtype
      (Sylow.smul_le hconjugatedSylow adjustment)) = localSylow := by
    exact (Sylow.smul_subtype hconjugatedSylow adjustment).symm.trans hadjustment
  have hglobalContained : (((adjustment : ambient) * conjugator) • sylow :
      Sylow prime ambient) ≤ overgroup := by
    rw [mul_smul]
    intro element helement
    let localElement : conjugate := ⟨element,
      Sylow.smul_le hconjugatedSylow adjustment helement⟩
    have hlocalElement : localElement ∈ localSylow := by
      rw [← hsubtype]
      exact helement
    exact hcontained (Subgroup.mem_map_of_mem conjugate.subtype hlocalElement)
  have hnormalizer : Subgroup.normalizer (sylow : Set ambient) ≤ overgroup :=
    (normalizer_le_weakCore_of_rank prime hprime (sylow : Subgroup ambient) hrank).trans hcore
  have hproduct : (adjustment : ambient) * conjugator ∈ overgroup :=
    (conjugated_sylow_le_iff_mem_of_normalizer_le prime sylow hsylow hnormalizer
      ((adjustment : ambient) * conjugator)).mp hglobalContained
  obtain ⟨member, hmember, hmemberEq⟩ := adjustment.property
  have hconjugatorMember : conjugator * member ∈ overgroup := by
    rw [← hmemberEq] at hproduct
    change (conjugator * member * conjugator⁻¹) * conjugator ∈ overgroup at hproduct
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hproduct
  exact hescape (by simpa only [mul_inv_cancel_right] using
    overgroup.mul_mem hconjugatorMember (overgroup.inv_mem hmember))

theorem escaping_GLBConj_intersection_rank_le_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (conjugator : ambient) (hescape : conjugator ∉ overgroup) :
    pRank prime (overgroup ⊓ GLBConj conjugator overgroup) ≤ 2 := by
  rw [inf_comm]
  exact escaping_conjugate_overgroup_intersection_rank_le_two prime hprime sylow
    hsylow hcore hrank conjugator⁻¹ (fun hcontained =>
      hescape (by simpa only [inv_inv] using overgroup.inv_mem hcontained))

end CFSG.PreuniquenessRankFour.Helpers
