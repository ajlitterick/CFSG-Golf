module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCore
public import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem pGroup_action_on_prime_order_group_trivial
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (hcard : Nat.card source = prime) : ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  have hfixedOne : (1 : source) ∈ MulAction.fixedPoints acting source := by
    intro scalar
    exact smul_one scalar
  obtain ⟨fixed, hfixed, hfixedNe⟩ :=
    hacting.exists_fixed_point_of_prime_dvd_card_of_fixed_point source
      (hcard ▸ dvd_refl prime) hfixedOne
  have hgenerator : Subgroup.zpowers fixed = ⊤ :=
    zpowers_eq_top_of_prime_card hcard hfixedNe.symm
  intro scalar member
  have hmember : member ∈ Subgroup.zpowers fixed := hgenerator ▸ Subgroup.mem_top member
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
  rw [smul_zpow', hfixed scalar]

theorem pGroup_action_on_elementary_rank_two_has_prime_index_kernel
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [CommGroup source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (hcard : Nat.card source = prime ^ 2) (hpow : ∀ member : source, member ^ prime = 1) :
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
      ∀ scalar ∈ kernel, ∀ member : source, scalar • member = member := by
  have hfixedOne : (1 : source) ∈ MulAction.fixedPoints acting source := fun scalar => smul_one scalar
  obtain ⟨fixed, hfixed, hfixedNe⟩ :=
    hacting.exists_fixed_point_of_prime_dvd_card_of_fixed_point source
      (hcard ▸ dvd_pow_self prime (by omega : 2 ≠ 0)) hfixedOne
  let line := Subgroup.zpowers fixed
  have hlineCard : Nat.card line = prime := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hpow fixed) hfixedNe.symm
  have hlineFixed : ∀ scalar : acting, ∀ member ∈ line, scalar • member = member := by
    intro scalar member hmember
    obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
    rw [smul_zpow', hfixed scalar]
  have hinvariant : ∀ scalar : acting, ∀ member ∈ line, scalar • member ∈ line := by
    intro scalar member hmember
    rw [hlineFixed scalar member hmember]
    exact hmember
  let : MulDistribMulAction acting (source ⧸ line) :=
    invariant_quotient_mulDistribMulAction line hinvariant
  have hquotientCard : Nat.card (source ⧸ line) = prime := by
    have hproduct := Subgroup.card_eq_card_quotient_mul_card_subgroup line
    rw [hcard, hlineCard, pow_two] at hproduct
    exact (Nat.mul_right_cancel (Fact.out : prime.Prime).pos hproduct.symm)
  have hquotientFixed := pGroup_action_on_prime_order_group_trivial prime hacting hquotientCard
  have hlineProper : line ≠ ⊤ := by
    intro hequal
    have hcards : prime = prime ^ 2 := by
      calc
        prime = Nat.card line := hlineCard.symm
        _ = Nat.card source := by rw [hequal, Subgroup.card_top]
        _ = prime ^ 2 := hcard
    have hlarge := Nat.lt_pow_self (Fact.out : prime.Prime).one_lt (n := 2)
    nlinarith
  obtain ⟨basisMember, hbasisMember⟩ : ∃ member : source, member ∉ line := by
    by_contra hnone
    push Not at hnone
    exact hlineProper (top_unique (fun member _ => hnone member))
  let displacement : acting →* source :=
    { toFun := fun scalar => (scalar • basisMember) * basisMember⁻¹
      map_one' := by simp
      map_mul' := by
        intro first second
        have hsecondLine : (second • basisMember) * basisMember⁻¹ ∈ line := by
          apply (QuotientGroup.eq_one_iff _).mp
          change (QuotientGroup.mk' line) ((second • basisMember) * basisMember⁻¹) = 1
          rw [map_mul, map_inv]
          have hfixedQuotient := hquotientFixed second ((QuotientGroup.mk' line) basisMember)
          change (QuotientGroup.mk' line) (second • basisMember) =
            (QuotientGroup.mk' line) basisMember at hfixedQuotient
          rw [hfixedQuotient, mul_inv_cancel]
        have hfix := hlineFixed first _ hsecondLine
        rw [smul_mul', smul_inv'] at hfix
        rw [mul_smul]
        calc
          _ = (first • basisMember) *
              ((first • (second • basisMember)) * (first • basisMember)⁻¹) *
                basisMember⁻¹ := by
                symm
                calc
                  _ = (first • second • basisMember) *
                      ((first • basisMember) * (first • basisMember)⁻¹) *
                        basisMember⁻¹ := by ac_rfl
                  _ = _ := by rw [mul_inv_cancel, mul_one]
          _ = (first • basisMember) * ((second • basisMember) * basisMember⁻¹) *
                basisMember⁻¹ := by rw [hfix]
          _ = _ := by ac_rfl }
  have hrangeLine : displacement.range ≤ line := by
    rintro member ⟨scalar, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' line) ((scalar • basisMember) * basisMember⁻¹) = 1
    have hfixedQuotient := hquotientFixed scalar ((QuotientGroup.mk' line) basisMember)
    change (QuotientGroup.mk' line) (scalar • basisMember) =
      (QuotientGroup.mk' line) basisMember at hfixedQuotient
    rw [map_mul, map_inv, hfixedQuotient, mul_inv_cancel]
  have hindex : displacement.ker.index = 1 ∨ displacement.ker.index = prime := by
    rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange displacement).toEquiv]
    exact (Fact.out : prime.Prime).eq_one_or_self_of_dvd _
      (hlineCard ▸ Subgroup.card_dvd_of_le hrangeLine)
  refine ⟨displacement.ker, hindex, ?_⟩
  intro scalar hscalar member
  have hbasisFixed : scalar • basisMember = basisMember := by
    have hdisplacement : (scalar • basisMember) * basisMember⁻¹ = 1 := hscalar
    exact mul_inv_eq_one.mp hdisplacement
  let fixedGroup := (MulDistribMulAction.toMulAut acting source scalar).toMonoidHom.eqLocus
    (MonoidHom.id source)
  have hlineLe : line ≤ fixedGroup := fun member hmember => hlineFixed scalar member hmember
  have hbasisLe : Subgroup.zpowers basisMember ≤ fixedGroup := Subgroup.zpowers_le.mpr hbasisFixed
  have hgenerates : line ⊔ Subgroup.zpowers basisMember = ⊤ := by
    have hquotientGenerator : Subgroup.zpowers ((QuotientGroup.mk' line) basisMember) = ⊤ :=
      zpowers_eq_top_of_prime_card hquotientCard (fun hone =>
        hbasisMember ((QuotientGroup.eq_one_iff basisMember).mp hone))
    have himage : (line ⊔ Subgroup.zpowers basisMember).map (QuotientGroup.mk' line) = ⊤ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers _ basisMember, hquotientGenerator, sup_top_eq]
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' line)) himage
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr le_sup_left,
      Subgroup.comap_top] at hcomap
    exact hcomap
  have htop : (⊤ : Subgroup source) ≤ fixedGroup := hgenerates ▸ sup_le hlineLe hbasisLe
  exact htop (Subgroup.mem_top member)

theorem normalizer_le_of_elementary_rank_two_normalized_by_rank_three
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary normal : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (helementaryContained : elementary ≤ overgroup)
    (hnormal : IsElemAbelian prime normal) (hnormalCard : Nat.card normal = prime ^ 2)
    (hnormalContained : normal ≤ overgroup)
    (hnormalized : elementary ≤ Subgroup.normalizer (normal : Set ambient)) :
    Subgroup.normalizer (normal : Set ambient) ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative normal := hnormal.1
  let : CommGroup normal := IsMulCommutative.instCommGroup
  let actionHom : elementary →* MulAut normal :=
    normal.normalizerMonoidHom.comp (Subgroup.inclusion hnormalized)
  let : MulDistribMulAction elementary normal := MulDistribMulAction.compHom normal actionHom
  obtain ⟨kernel, hindex, hfixed⟩ :=
    pGroup_action_on_elementary_rank_two_has_prime_index_kernel prime (IsPGroup.of_card hcard)
      hnormalCard (fun member => by apply Subtype.ext; exact hnormal.2 member member.property)
  let kernelAmbient := kernel.map elementary.subtype
  have hkernelElementary : IsElemAbelian prime kernelAmbient := by
    let : IsMulCommutative elementary := helementary.1
    have hkernel : IsElemAbelian prime kernel :=
      ⟨inferInstance, fun member hmember => by
        apply Subtype.ext
        exact helementary.2 member member.property⟩
    exact elementary_abelian_map prime hkernel elementary.subtype
  have hkernelCentral : kernelAmbient ≤ Subgroup.centralizer (normal : Set ambient) := by
    rintro member ⟨scalar, hscalar, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hequal := congrArg Subtype.val (hfixed scalar hscalar (⟨other, hother⟩ : normal))
    change (scalar : ambient) * other * (scalar : ambient)⁻¹ = other at hequal
    exact (mul_inv_eq_iff_eq_mul.mp hequal).symm
  have hkernelRank : 2 ≤ pRank prime kernelAmbient :=
    (show 2 ≤ rank - 1 by omega).trans
      (elementary_prime_index_subgroup_rank prime hprime helementary rank hcard kernel hindex)
  let joinGroup := normal ⊔ kernelAmbient
  have hjoinElementary : IsElemAbelian prime joinGroup :=
    elementary_abelian_sup_of_commuting prime hnormal hkernelElementary
      (Subgroup.le_centralizer_iff.mp hkernelCentral)
  have hjoinContained : joinGroup ≤ overgroup :=
    sup_le hnormalContained ((Subgroup.map_subtype_le kernel).trans helementaryContained)
  by_cases hjoinRank : 3 ≤ pRank prime joinGroup
  · have hnormalRank : 2 ≤ pRank prime normal :=
      le_csSup (pRank_bddAbove prime hprime normal) ⟨normal, le_rfl, hnormal, hnormalCard⟩
    have hjoinCentral : joinGroup ≤ Subgroup.centralizer (normal : Set ambient) :=
      sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hnormal.1) hkernelCentral
    have hcentralRank : 3 ≤ pRank prime
        (overgroup ⊓ Subgroup.centralizer (normal : Set ambient)) :=
      hjoinRank.trans (pRank_mono prime hprime (le_inf hjoinContained hjoinCentral))
    exact normalizer_le_of_subgroup_and_centralizer_rank prime hprime sylow hsylow hcore
      hnormalContained hnormalRank hcentralRank
  · have hnormalJoin : normal = joinGroup :=
      elementary_subgroup_eq_of_rank_bound prime hprime hjoinElementary le_sup_left
        2 hnormalCard (by omega)
    have hkernelNormal : kernelAmbient ≤ normal := hnormalJoin ▸ le_sup_right
    have hkernelGroup : IsPGroup prime kernelAmbient := by
      exact (IsPGroup.of_card hnormalCard).to_le hkernelNormal
    obtain ⟨kernelRank, hkernelCard⟩ := IsPGroup.iff_card.mp hkernelGroup
    have hkernelRankLower : 2 ≤ kernelRank := by
      have hbound : pRank prime kernelAmbient ≤ kernelRank := by
        apply csSup_le'
        rintro candidateRank ⟨candidate, hcandidate, _, hcandidateCard⟩
        have hle := Subgroup.card_le_of_le hcandidate
        rw [hcandidateCard, hkernelCard] at hle
        exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp hle
      exact hkernelRank.trans hbound
    have hkernelEq : kernelAmbient = normal := by
      apply Subgroup.eq_of_le_of_card_ge hkernelNormal
      rw [hnormalCard, hkernelCard]
      exact Nat.pow_le_pow_right hprime.pos hkernelRankLower
    have hnormalElementary : normal ≤ elementary := hkernelEq ▸ Subgroup.map_subtype_le kernel
    have hcentral : elementary ≤ Subgroup.centralizer (normal : Set ambient) :=
      commutative_subgroup_le_centralizer helementary.1 hnormalElementary
    have hcentralRank : 3 ≤ pRank prime
        (overgroup ⊓ Subgroup.centralizer (normal : Set ambient)) :=
      hrank.trans (le_csSup (pRank_bddAbove prime hprime _)
        ⟨elementary, le_inf helementaryContained hcentral, helementary, hcard⟩)
    exact normalizer_le_of_subgroup_and_centralizer_rank prime hprime sylow hsylow hcore
      hnormalContained (le_csSup (pRank_bddAbove prime hprime normal)
        ⟨normal, le_rfl, hnormal, hnormalCard⟩) hcentralRank


theorem pRank_sylow_eq_globalRank
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient) :
    pRank prime (sylow : Subgroup ambient) = pRank prime (⊤ : Subgroup ambient) := by
  let : Fact prime.Prime := ⟨hprime⟩
  apply le_antisymm (pRank_mono prime hprime le_top)
  obtain ⟨elementary, _, helementary, hcard⟩ := pRank_attained prime hprime (⊤ : Subgroup ambient)
  obtain ⟨conjugator, hcontained⟩ := exists_conjugate_le_sylow_of_le prime sylow
    (overgroup := ⊤) le_top le_top (IsPGroup.of_card hcard)
  let hom := (MulAut.conj (conjugator : ambient)).toMonoidHom
  exact le_csSup (pRank_bddAbove prime hprime (sylow : Subgroup ambient))
    ⟨elementary.map hom, hcontained, elementary_abelian_map prime helementary hom,
      (Subgroup.card_map_of_injective (f := hom) (MulAut.conj (conjugator : ambient)).injective).trans hcard⟩

theorem betaFour_all_sylows_rank_ge_four
    {ambient : Type u} [Group ambient] [Finite ambient]
    {prime : ℕ} (hprime : prime ∈ GLBBetaFour ambient) (sylow : Sylow prime ambient) :
    4 ≤ pRank prime (sylow : Subgroup ambient) := by
  rw [pRank_sylow_eq_globalRank prime hprime.1 sylow]
  exact betaFour_globalRank hprime

theorem normal_section_elementary_rank_two_forces_containment
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (normal : Subgroup source) [normal.Normal]
    (kernel : Subgroup normal) [kernel.Normal]
    (hcoprime : ¬ prime ∣ Nat.card kernel)
    (hsection : IsElemAbelian prime (⊤ : Subgroup (normal ⧸ kernel)))
    (hsectionCard : Nat.card (normal ⧸ kernel) = prime ^ 2)
    (hnormalContained : normal.map source.subtype ≤ overgroup) : source ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let normalAmbient := normal.map source.subtype
  have hnormalizer : source ≤ Subgroup.normalizer (normalAmbient : Set ambient) := by
    have hnormalLocal : (normalAmbient.subgroupOf source).Normal := by
      rw [show normalAmbient.subgroupOf source = normal from
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective normal]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le normal)).mp hnormalLocal
  obtain ⟨acting, hactingContained, hacting, hactingCard⟩ :=
    pRank_attained prime hprime (source ⊓ overgroup)
  obtain ⟨invariantSylow, hinvariantSylow⟩ := exists_normalized_same_prime_sylow prime
    (IsPGroup.of_card hactingCard) ((hactingContained.trans inf_le_left).trans hnormalizer)
  let ambientElementary := (invariantSylow : Subgroup normalAmbient).map normalAmbient.subtype
  let normalEquivalence : normal ≃* normalAmbient :=
    normal.equivMapOfInjective source.subtype Subtype.val_injective
  let originalSylow := invariantSylow.comapOfInjective normalEquivalence.toMonoidHom
    normalEquivalence.injective (by rw [MonoidHom.range_eq_top.mpr normalEquivalence.surjective]; exact le_top)
  obtain ⟨sectionEquivalence⟩ := sylow_quotient_equivalence_of_coprime_kernel prime kernel hcoprime
    (IsPGroup.of_card hsectionCard) originalSylow
  have hinvariantImage : (originalSylow : Subgroup normal).map normalEquivalence.toMonoidHom =
      (invariantSylow : Subgroup normalAmbient) := by
    have hcomap : (originalSylow : Subgroup normal) =
        (invariantSylow : Subgroup normalAmbient).comap normalEquivalence.toMonoidHom :=
      Sylow.coe_comapOfInjective invariantSylow normalEquivalence.toMonoidHom
        normalEquivalence.injective _
    rw [hcomap, Subgroup.map_comap_eq_self_of_surjective normalEquivalence.surjective]
  let sylowEquivalence : (originalSylow : Subgroup normal) ≃* (invariantSylow : Subgroup normalAmbient) :=
    (originalSylow : Subgroup normal).equivMapOfInjective normalEquivalence.toMonoidHom
      normalEquivalence.injective |>.trans (MulEquiv.subgroupCongr hinvariantImage)
  let equivalence : (invariantSylow : Subgroup normalAmbient) ≃* (normal ⧸ kernel) :=
    sylowEquivalence.symm.trans sectionEquivalence
  let : IsMulCommutative (normal ⧸ kernel) :=
    IsMulCommutative.of_comm (fun first second => by
      have hcomm := isMulCommutative_iff.mp hsection.1
      exact congrArg Subtype.val (hcomm (⟨first, Subgroup.mem_top _⟩ : (⊤ : Subgroup (normal ⧸ kernel)))
        ⟨second, Subgroup.mem_top _⟩))
  have hsylowElementary : IsElemAbelian prime (invariantSylow : Subgroup normalAmbient) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro first second
      apply equivalence.injective
      rw [map_mul, map_mul]
      exact (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (normal ⧸ kernel))) _ _
    · intro member hmember
      have hequal : (⟨member, hmember⟩ : (invariantSylow : Subgroup normalAmbient)) ^ prime = 1 := by
        apply equivalence.injective
        rw [map_pow, map_one]
        exact hsection.2 _ (Subgroup.mem_top _)
      exact congrArg Subtype.val hequal
  have hambientElementary : IsElemAbelian prime ambientElementary :=
    elementary_abelian_map prime hsylowElementary normalAmbient.subtype
  have hambientCard : Nat.card ambientElementary = prime ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := normalAmbient.subtype) Subtype.val_injective,
      Nat.card_congr equivalence.toEquiv, hsectionCard]
  have helementaryNormalizer : Subgroup.normalizer (ambientElementary : Set ambient) ≤ overgroup :=
    normalizer_le_of_elementary_rank_two_normalized_by_rank_three prime hprime sylow hsylow hcore
      hacting (pRank prime (source ⊓ overgroup)) hrank hactingCard
      (hactingContained.trans inf_le_right) hambientElementary hambientCard
      ((Subgroup.map_subtype_le (invariantSylow : Subgroup normalAmbient)).trans hnormalContained)
      hinvariantSylow
  let liftedSylow := Sylow.mapSurjective (f := normalEquivalence.toMonoidHom)
    normalEquivalence.surjective originalSylow
  have hliftedSylow : (liftedSylow : Subgroup normalAmbient) = invariantSylow := by
    exact (Sylow.coe_mapSurjective normalEquivalence.surjective originalSylow).trans hinvariantImage
  let normalLocal := normalAmbient.subgroupOf source
  let : normalLocal.Normal := by
    rw [show normalLocal = normal from
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective normal]
    infer_instance
  let normalLocalEquivalence : normalAmbient ≃* normalLocal :=
    (normalAmbient.subgroupOfEquivOfLe (Subgroup.map_subtype_le normal)).symm
  let sourceSylow := Sylow.mapSurjective (f := normalLocalEquivalence.toMonoidHom)
    normalLocalEquivalence.surjective liftedSylow
  let sourceSylowAmbient := ((sourceSylow : Subgroup normalLocal).map normalLocal.subtype).map source.subtype
  have hsourceSylowAmbient : sourceSylowAmbient = ambientElementary := by
    have hmap : (sourceSylow : Subgroup normalLocal) =
        (liftedSylow : Subgroup normalAmbient).map normalLocalEquivalence.toMonoidHom :=
      Sylow.coe_mapSurjective normalLocalEquivalence.surjective liftedSylow
    change ((sourceSylow : Subgroup normalLocal).map normalLocal.subtype).map source.subtype =
      (invariantSylow : Subgroup normalAmbient).map normalAmbient.subtype
    rw [hmap, Subgroup.map_map, Subgroup.map_map, hliftedSylow]
    congr 1
  have hnormalizerSource : Subgroup.normalizer
      ((sourceSylow : Subgroup normalLocal).map normalLocal.subtype : Set source) ≤
        overgroup.subgroupOf source := by
    intro member hmember
    have hmap := Subgroup.le_normalizer_map source.subtype
      (Subgroup.mem_map_of_mem source.subtype hmember)
    change (member : ambient) ∈ Subgroup.normalizer (sourceSylowAmbient : Set ambient) at hmap
    rw [hsourceSylowAmbient] at hmap
    exact helementaryNormalizer hmap
  have hnormalLocalContained : normalLocal ≤ overgroup.subgroupOf source := by
    intro member hmember
    exact hnormalContained hmember
  have htop : (⊤ : Subgroup source) ≤ overgroup.subgroupOf source := by
    rw [← sourceSylow.normalizer_sup_eq_top]
    exact sup_le hnormalizerSource hnormalLocalContained
  exact Subgroup.subgroupOf_eq_top.mp (top_unique htop)

theorem escaping_rank_three_primeCore_quotient_has_no_normal_elementary_rank_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (helementary : IsElemAbelian prime normal) : Nat.card normal ≠ prime ^ 2 := by
  intro hcard
  let radical := (GLBPrimeCore prime source).subgroupOf source
  let hom := QuotientGroup.mk' radical
  let lifted := normal.comap hom
  let : lifted.Normal := inferInstance
  let restricted := hom.subgroupMap lifted
  have hradicalLift : radical ≤ lifted := by
    intro member hmember
    change hom member ∈ normal
    rw [show hom member = 1 from (QuotientGroup.eq_one_iff member).mpr hmember]
    exact normal.one_mem
  have hkernel : restricted.ker = radical.subgroupOf lifted := by
    ext member
    change (⟨hom member, _⟩ : lifted.map hom) = 1 ↔ (member : source) ∈ radical
    rw [Subtype.ext_iff]
    exact @QuotientGroup.eq_one_iff source _ radical _ member
  have hcoprime : ¬ prime ∣ Nat.card restricted.ker := by
    rw [hkernel, Nat.card_congr (radical.subgroupOfEquivOfLe hradicalLift).toEquiv,
      Nat.card_congr ((GLBPrimeCore prime source).subgroupOfEquivOfLe
        (primeCore_le prime source)).toEquiv]
    exact hprime.coprime_iff_not_dvd.mp (primeCore_coprime prime hprime source)
  have himage : lifted.map hom = normal :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective radical) normal
  let equivalence : (lifted ⧸ restricted.ker) ≃* normal :=
    (QuotientGroup.quotientKerEquivOfSurjective restricted
      (hom.subgroupMap_surjective lifted)).trans (MulEquiv.subgroupCongr himage)
  have hsection : IsElemAbelian prime (⊤ : Subgroup (lifted ⧸ restricted.ker)) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro first second
      apply Subtype.ext
      apply equivalence.injective
      change equivalence ((first : lifted ⧸ restricted.ker) * second) =
        equivalence ((second : lifted ⧸ restricted.ker) * first)
      rw [map_mul, map_mul]
      exact (isMulCommutative_iff.mp helementary.1) _ _
    · intro member _
      apply equivalence.injective
      rw [map_pow, map_one]
      exact Subtype.ext (helementary.2 _ (equivalence member).property)
  have hsectionCard : Nat.card (lifted ⧸ restricted.ker) = prime ^ 2 :=
    (Nat.card_congr equivalence.toEquiv).trans hcard
  have hcontained : lifted.map source.subtype ≤ overgroup :=
    intersecting_rank_three_primeCore_quotient_normal_primeSubgroup_lift_le prime hprime sylow
      hsylow hcore hrank normal (IsPGroup.of_card hcard)
  exact hescape (normal_section_elementary_rank_two_forces_containment prime hprime sylow
    hsylow hcore hrank lifted restricted.ker hcoprime hsection hsectionCard hcontained)

theorem escaping_rank_three_primeCore_quotient_normal_elementary_rank_le_one
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (helementary : IsElemAbelian prime normal) : pRank prime normal ≤ 1 := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hnormalGroup : IsPGroup prime normal := isPGroup_iff_pow_pow_eq_one.mpr fun member =>
    ⟨1, by
      apply Subtype.ext
      change (member : source ⧸ (GLBPrimeCore prime source).subgroupOf source) ^ (prime ^ 1) = 1
      simpa only [pow_one] using helementary.2 member member.property⟩
  have hbound := escaping_rank_three_primeCore_quotient_normal_primeSubgroup_rank_le_two
    prime hprime sylow hsylow hcore hrank hescape normal hnormalGroup
  obtain ⟨normalRank, hcard⟩ := IsPGroup.iff_card.mp hnormalGroup
  have hnormalRank : normalRank ≤ pRank prime normal :=
    le_csSup (pRank_bddAbove prime hprime normal) ⟨normal, le_rfl, helementary, hcard⟩
  have hrankCardUpper : pRank prime normal ≤ normalRank := by
    obtain ⟨attaining, hcontained, _, hattainingCard⟩ := pRank_attained prime hprime normal
    have hcardLe := Subgroup.card_le_of_le hcontained
    rw [hattainingCard, hcard] at hcardLe
    exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp hcardLe
  have hnotTwo := escaping_rank_three_primeCore_quotient_has_no_normal_elementary_rank_two
    prime hprime sylow hsylow hcore hrank hescape normal helementary
  have hnormalRankNe : normalRank ≠ 2 := fun hequal => hnotTwo (hequal ▸ hcard)
  omega


theorem odd_cyclic_pGroup_mulAut_isCyclic
    {source : Type u} [Group source] [Finite source] [IsCyclic source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hgroup : IsPGroup prime source) : IsCyclic (MulAut source) := by
  obtain ⟨exponent, hcard⟩ := hgroup.exists_card_eq
  let : IsCyclic (ZMod (Nat.card source))ˣ := by
    rw [hcard]
    exact ZMod.isCyclic_units_of_prime_pow prime Fact.out hodd exponent
  exact (IsCyclic.mulAutMulEquiv source).isCyclic.mpr inferInstance

theorem cyclic_group_of_prime_exponent_card_eq_one_or_prime
    {source : Type u} [Group source] [Finite source] [IsCyclic source]
    (prime : ℕ) [Fact prime.Prime] (hpow : ∀ member : source, member ^ prime = 1) :
    Nat.card source = 1 ∨ Nat.card source = prime := by
  obtain ⟨generator, hgenerator⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := source)
  have hdivides : Nat.card source ∣ prime := by
    rw [← hgenerator]
    exact orderOf_dvd_of_pow_eq_one (hpow generator)
  exact (Nat.dvd_prime (Fact.out : prime.Prime)).mp hdivides

theorem elementary_action_on_odd_cyclic_pGroup_has_prime_index_kernel
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source] [IsCyclic source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hsource : IsPGroup prime source) (hpow : ∀ scalar : acting, scalar ^ prime = 1) :
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
      ∀ scalar ∈ kernel, ∀ member : source, scalar • member = member := by
  let actionHom := MulDistribMulAction.toMulAut acting source
  let : IsCyclic (MulAut source) := odd_cyclic_pGroup_mulAut_isCyclic prime hodd hsource
  have himagePow : ∀ member : actionHom.range, member ^ prime = 1 := by
    rintro ⟨member, scalar, rfl⟩
    apply Subtype.ext
    change actionHom scalar ^ prime = 1
    rw [← map_pow, hpow scalar, map_one]
  have hcard := cyclic_group_of_prime_exponent_card_eq_one_or_prime prime himagePow
  refine ⟨actionHom.ker, ?_, ?_⟩
  · rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange actionHom).toEquiv]
    exact hcard
  · intro scalar hscalar member
    have hfixed := congrArg (fun equivalence : MulAut source => equivalence member)
      (show actionHom scalar = 1 from hscalar)
    exact hfixed


end CFSG.PreuniquenessRankFour.Helpers
