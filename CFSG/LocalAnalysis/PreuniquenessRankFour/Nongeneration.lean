module

public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem pRank_map_of_injective
    {source : Type u} {target : Type v} [Group source] [Finite source]
    [Group target] [Finite target]
    (prime : ℕ) (hprime : prime.Prime) (hom : source →* target)
    (hinjective : Function.Injective hom) (subgroup : Subgroup source) :
    pRank prime (subgroup.map hom) = pRank prime subgroup := by
  apply le_antisymm
  · obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
      pRank_attained prime hprime (subgroup.map hom)
    let lifted := elementary.comap hom
    have hmap : lifted.map hom = elementary :=
      Subgroup.map_comap_eq_self (hcontained.trans (by
        rintro element ⟨lift, _, rfl⟩
        exact ⟨lift, rfl⟩))
    have hlifted : lifted ≤ subgroup := by
      have hle := Subgroup.comap_mono (f := hom) hcontained
      rwa [Subgroup.comap_map_eq_self_of_injective hinjective] at hle
    have hliftedElementary : IsElemAbelian prime lifted := by
      let : IsMulCommutative elementary := helementary.1
      refine ⟨Subgroup.comap_injective_isMulCommutative elementary hinjective, ?_⟩
      intro element helement
      apply hinjective
      rw [map_pow, helementary.2 (hom element) helement, map_one]
    apply le_csSup (pRank_bddAbove prime hprime subgroup)
    refine ⟨lifted, hlifted, hliftedElementary, ?_⟩
    rw [← Subgroup.card_map_of_injective hinjective, hmap, hcard]
  · obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
      pRank_attained prime hprime subgroup
    apply le_csSup (pRank_bddAbove prime hprime (subgroup.map hom))
    refine ⟨elementary.map hom, Subgroup.map_mono hcontained,
      elementary_abelian_map prime helementary hom, ?_⟩
    rw [Subgroup.card_map_of_injective hinjective, hcard]

theorem elementary_rank_le_kernel_rank_add_image_rank
    {source : Type u} {target : Type v} [Group source] [Finite source]
    [Group target] [Finite target]
    (prime : ℕ) (hprime : prime.Prime) (hom : source →* target)
    {elementary : Subgroup source} (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hcard : Nat.card elementary = prime ^ rank) :
    rank ≤ pRank prime hom.ker + pRank prime (elementary.map hom) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative elementary := helementary.1
  let restricted := hom.comp elementary.subtype
  have hkernelElementary : IsElemAbelian prime restricted.ker := by
    refine ⟨inferInstance, ?_⟩
    intro element _
    apply Subtype.ext
    exact helementary.2 element element.property
  have hkernelGroup : IsPGroup prime restricted.ker :=
    (IsPGroup.of_card hcard).to_subgroup restricted.ker
  have himageElementary : IsElemAbelian prime restricted.range := by
    have hrange : restricted.range = elementary.map hom := by
      exact (MonoidHom.range_comp hom elementary.subtype).trans
        (congrArg (Subgroup.map hom) elementary.range_subtype)
    exact hrange ▸ elementary_abelian_map prime helementary hom
  have himageGroup : IsPGroup prime restricted.range := by
    have hsurjective : Function.Surjective restricted.rangeRestrict :=
      restricted.rangeRestrict_surjective
    exact (IsPGroup.of_card hcard).of_surjective restricted.rangeRestrict hsurjective
  obtain ⟨kernelRank, hkernelCard⟩ := IsPGroup.iff_card.mp hkernelGroup
  obtain ⟨imageRank, himageCard⟩ := IsPGroup.iff_card.mp himageGroup
  have hsum : rank = kernelRank + imageRank := by
    have hproduct := restricted.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange restricted).toEquiv,
      hcard, hkernelCard, himageCard, ← pow_add] at hproduct
    have hequal := Nat.pow_right_injective hprime.two_le hproduct
    omega
  have hkernelAmbient : restricted.ker.map elementary.subtype ≤ hom.ker := by
    rintro element ⟨lift, hlift, rfl⟩
    exact hlift
  have hkernelRank : kernelRank ≤ pRank prime hom.ker := by
    apply le_csSup (pRank_bddAbove prime hprime hom.ker)
    refine ⟨restricted.ker.map elementary.subtype, hkernelAmbient,
      elementary_abelian_map prime hkernelElementary elementary.subtype, ?_⟩
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hkernelCard]
  have himageRank : imageRank ≤ pRank prime (elementary.map hom) := by
    apply le_csSup (pRank_bddAbove prime hprime (elementary.map hom))
    refine ⟨restricted.range, ?_, himageElementary, himageCard⟩
    rintro element ⟨lift, rfl⟩
    exact ⟨lift, lift.property, rfl⟩
  omega


theorem normal_solvable_subgroup_contains_normal_primeSubgroup
    {source : Type u} [Group source] [Finite source]
    (normal : Subgroup source) [normal.Normal] [Group.IsSolvable normal]
    (hnontrivial : normal ≠ ⊥) :
    ∃ prime : ℕ, prime.Prime ∧ ∃ subgroup : Subgroup source,
      subgroup.Normal ∧ subgroup ≠ ⊥ ∧ subgroup ≤ normal ∧ IsPGroup prime subgroup := by
  obtain ⟨subgroup, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊥ ∧ candidate ≤ normal)
    (a := normal) ⟨inferInstance, hnontrivial, le_rfl⟩
  let : subgroup.Normal := hminimal.1.1
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.1.2.1
  let : Group.IsSolvable subgroup := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hminimal.1.2.2) (Subgroup.inclusion_injective hminimal.1.2.2)
  have hcommutatorNormal : ((commutator subgroup).map subgroup.subtype).Normal := inferInstance
  have hcommutatorBot : (commutator subgroup).map subgroup.subtype = ⊥ := by
    by_contra hnontrivial
    have hminimalLe := hminimal.2 ⟨hcommutatorNormal, hnontrivial,
      (Subgroup.map_subtype_le (commutator subgroup)).trans hminimal.1.2.2⟩
      (Subgroup.map_subtype_le (commutator subgroup))
    have htop : commutator subgroup = ⊤ := by
      apply top_unique
      intro element _
      obtain ⟨lift, hlift, hequal⟩ := hminimalLe element.property
      exact (Subtype.ext hequal : lift = element) ▸ hlift
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial subgroup).ne htop
  have hcommutator : commutator subgroup = ⊥ := by
    apply (Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective)
    simpa only [Subgroup.map_bot] using hcommutatorBot
  let : IsMulCommutative subgroup := (commutator_eq_bot_iff subgroup).mp hcommutator
  obtain ⟨prime, hprime, hdivides⟩ := Nat.exists_prime_and_dvd
    (show Nat.card subgroup ≠ 1 from by
      intro hone
      exact hminimal.1.2.1 (Subgroup.card_eq_one.mp hone))
  let : Fact prime.Prime := ⟨hprime⟩
  let sylow : Sylow prime subgroup := Classical.choice inferInstance
  have hsylowNontrivial : (sylow : Subgroup subgroup) ≠ ⊥ := sylow.ne_bot_of_dvd_card hdivides
  have hsylowNormal : (sylow : Subgroup subgroup).Normal := inferInstance
  let : (sylow : Subgroup subgroup).Characteristic := sylow.characteristic_of_normal hsylowNormal
  have hmapNormal : ((sylow : Subgroup subgroup).map subgroup.subtype).Normal := inferInstance
  have hmapNontrivial : (sylow : Subgroup subgroup).map subgroup.subtype ≠ ⊥ := by
    intro hbot
    apply hsylowNontrivial
    apply (Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective)
    simpa only [Subgroup.map_bot] using hbot
  have hmapEq : (sylow : Subgroup subgroup).map subgroup.subtype = subgroup :=
    le_antisymm (Subgroup.map_subtype_le _) (hminimal.2 ⟨hmapNormal, hmapNontrivial,
      (Subgroup.map_subtype_le _).trans hminimal.1.2.2⟩
      (Subgroup.map_subtype_le _))
  refine ⟨prime, hprime, subgroup, hminimal.1.1, hminimal.1.2.1, hminimal.1.2.2, ?_⟩
  exact hmapEq ▸ (sylow.isPGroup'.map subgroup.subtype)


noncomputable abbrev invariant_quotient_mulDistribMulAction
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [MulDistribMulAction acting source]
    (normal : Subgroup source) [normal.Normal]
    (hinvariant : ∀ scalar : acting, ∀ element ∈ normal, scalar • element ∈ normal) :
    MulDistribMulAction acting (source ⧸ normal) := by
  let : MulAction.QuotientAction acting normal :=
    ⟨fun scalar first second hmember => by
      simpa only [smul_mul', smul_inv'] using hinvariant scalar (first⁻¹ * second) hmember⟩
  exact
    { toMulAction := MulAction.quotient acting normal
      smul_one := fun scalar => by
        change (QuotientGroup.mk' normal) (scalar • 1) = (QuotientGroup.mk' normal) 1
        rw [smul_one]
      smul_mul := fun scalar first second => by
        obtain ⟨firstLift, rfl⟩ := QuotientGroup.mk'_surjective normal first
        obtain ⟨secondLift, rfl⟩ := QuotientGroup.mk'_surjective normal second
        change (QuotientGroup.mk' normal) (scalar • (firstLift * secondLift)) =
          (QuotientGroup.mk' normal) (scalar • firstLift) *
            (QuotientGroup.mk' normal) (scalar • secondLift)
        rw [smul_mul', map_mul] }


theorem minimal_normal_map_mulEquiv
    {source : Type u} {target : Type v} [Group source] [Group target]
    (equivalence : source ≃* target) (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup) :
    Minimal (fun candidate : Subgroup target => candidate.Normal ∧ candidate ≠ ⊥)
      (subgroup.map equivalence.toMonoidHom) := by
  have hmapNontrivial : subgroup.map equivalence.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hminimal.1.2
    apply Subgroup.map_injective (f := equivalence.toMonoidHom) equivalence.injective
    simpa only [Subgroup.map_bot] using hbot
  refine ⟨⟨hminimal.1.1.map equivalence.toMonoidHom equivalence.surjective,
    hmapNontrivial⟩, ?_⟩
  intro candidate hcandidate hcontained
  have hcomapNontrivial : candidate.comap equivalence.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hmap := Subgroup.map_comap_eq_self_of_surjective
      (f := equivalence.toMonoidHom) equivalence.surjective candidate
    rw [hbot, Subgroup.map_bot] at hmap
    exact hcandidate.2 hmap.symm
  have hcomapLe : candidate.comap equivalence.toMonoidHom ≤ subgroup := by
    have hle := Subgroup.comap_mono (f := equivalence.toMonoidHom) hcontained
    rwa [Subgroup.comap_map_eq_self_of_injective equivalence.injective] at hle
  have hminimalLe := hminimal.2
    ⟨hcandidate.1.comap equivalence.toMonoidHom, hcomapNontrivial⟩ hcomapLe
  have hmapLe := Subgroup.map_mono (f := equivalence.toMonoidHom) hminimalLe
  rwa [Subgroup.map_comap_eq_self_of_surjective
    (f := equivalence.toMonoidHom) equivalence.surjective] at hmapLe

theorem distinct_minimal_normal_subgroups_commute
    {source : Type u} [Group source]
    (first second : Subgroup source)
    (hfirst : Minimal (fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊥) first)
    (hsecond : Minimal (fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊥) second)
    (hdistinct : first ≠ second) :
    first ≤ Subgroup.centralizer (second : Set source) := by
  let : first.Normal := hfirst.1.1
  let : second.Normal := hsecond.1.1
  have hdisjoint : Disjoint first second := by
    apply disjoint_iff.mpr
    by_contra hnotBot
    have hnontrivial : first ⊓ second ≠ ⊥ := by
      intro hbot
      exact hnotBot hbot
    have hfirstLe := hfirst.2 ⟨inferInstance, hnontrivial⟩ inf_le_left
    have hsecondLe := hsecond.2 ⟨inferInstance, hnontrivial⟩ inf_le_right
    exact hdistinct (le_antisymm (hfirstLe.trans inf_le_right) (hsecondLe.trans inf_le_left))
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact (Subgroup.commute_of_normal_of_disjoint first second hfirst.1.1 hsecond.1.1
    hdisjoint element other helement hother).eq.symm

theorem minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless
    {source : Type u} [Group source] [Finite source]
    (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup) :
    ∃ simple : Subgroup subgroup,
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) simple ∧ IsSimpleGroup simple ∧
        (Subgroup.center subgroup = ⊥ → ∃ first second : simple,
          first * second ≠ second * first) ∧
        (∀ prime : ℕ, prime.Prime → prime ∣ Nat.card subgroup → prime ∣ Nat.card simple) := by
  let : subgroup.Normal := hminimal.1.1
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.1.2
  obtain ⟨simple, _, hsimpleMinimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊥)
    (a := ⊤) ⟨inferInstance, top_ne_bot⟩
  let : simple.Normal := hsimpleMinimal.1.1
  let : Nontrivial simple := simple.nontrivial_iff_ne_bot.mpr hsimpleMinimal.1.2
  let normalizerHom : source →* Subgroup.normalizer (subgroup : Set source) :=
    { toFun := fun element => ⟨element, by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let conjugation : source →* MulAut subgroup :=
    subgroup.normalizerMonoidHom.comp normalizerHom
  let conjugate : source → Subgroup subgroup :=
    fun element => simple.map (conjugation element).toMonoidHom
  have hconjugateMinimal : ∀ element, Minimal
      (fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊥)
      (conjugate element) := fun element =>
    minimal_normal_map_mulEquiv (conjugation element) simple hsimpleMinimal
  let generated := ⨆ element : source, (conjugate element).map subgroup.subtype
  have hgeneratedNormal : generated.Normal := by
    refine ⟨?_⟩
    intro member hmember element
    have hmapLe : generated.map (MulAut.conj element).toMonoidHom ≤ generated := by
      change (⨆ scalar : source, (conjugate scalar).map subgroup.subtype).map
        (MulAut.conj element).toMonoidHom ≤ generated
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro other
      have hmapEq : ((conjugate other).map subgroup.subtype).map
          (MulAut.conj element).toMonoidHom = (conjugate (element * other)).map subgroup.subtype := by
        change ((simple.map (conjugation other).toMonoidHom).map subgroup.subtype).map
          (MulAut.conj element).toMonoidHom =
            (simple.map (conjugation (element * other)).toMonoidHom).map subgroup.subtype
        rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext value
        rw [map_mul]
        change element * (subgroup.subtype ((conjugation other) value)) * element⁻¹ =
          subgroup.subtype ((conjugation element) ((conjugation other) value))
        exact (subgroup.normalizerMonoidHom_apply_apply_coe ⟨element, by
          rw [Subgroup.normalizer_eq_top]
          exact Subgroup.mem_top _⟩ ((conjugation other) value)).symm
      rw [hmapEq]
      exact le_iSup (fun scalar => (conjugate scalar).map subgroup.subtype) (element * other)
    exact hmapLe (Subgroup.mem_map_of_mem (MulAut.conj element).toMonoidHom hmember)
  let : generated.Normal := hgeneratedNormal
  have hgeneratedContained : generated ≤ subgroup := iSup_le fun _ => Subgroup.map_subtype_le _
  have hsimpleGenerated : simple.map subgroup.subtype ≤ generated := by
    have hone : conjugate 1 = simple := by
      change simple.map (conjugation 1).toMonoidHom = simple
      rw [map_one]
      exact Subgroup.map_id simple
    rw [← hone]
    exact le_iSup (fun scalar => (conjugate scalar).map subgroup.subtype) 1
  have hgeneratedNontrivial : generated ≠ ⊥ := by
    intro hbot
    have hsimpleBot : simple.map subgroup.subtype = ⊥ := bot_unique (hbot ▸ hsimpleGenerated)
    apply hsimpleMinimal.1.2
    apply Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective
    simpa only [Subgroup.map_bot] using hsimpleBot
  have hgeneratedEq : generated = subgroup :=
    le_antisymm hgeneratedContained (hminimal.2 ⟨hgeneratedNormal, hgeneratedNontrivial⟩
      hgeneratedContained)
  have hprimeTransfer : ∀ prime : ℕ, prime.Prime → prime ∣ Nat.card subgroup →
      prime ∣ Nat.card simple := by
    intro prime hprime hdivides
    let factors : Set (Subgroup subgroup) := Set.range conjugate
    let : Fintype factors := Fintype.ofFinite factors
    have hfactorMinimal : ∀ factor : factors, Minimal
        (fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊥)
        (factor : Subgroup subgroup) := by
      intro factor
      obtain ⟨element, hequal⟩ := factor.property
      exact hequal ▸ hconjugateMinimal element
    have hfactorComm : Pairwise fun first second : factors =>
        ∀ (firstElement : (first : Subgroup subgroup)) (secondElement : (second : Subgroup subgroup)),
          Commute ((first : Subgroup subgroup).subtype firstElement)
            ((second : Subgroup subgroup).subtype secondElement) := by
      intro first second hdistinct firstElement secondElement
      have hne : (first : Subgroup subgroup) ≠ (second : Subgroup subgroup) := by
        intro hequal
        exact hdistinct (Subtype.ext hequal)
      exact (Subgroup.mem_centralizer_iff.mp
        ((distinct_minimal_normal_subgroups_commute (first : Subgroup subgroup)
          (second : Subgroup subgroup)
          (hfactorMinimal first) (hfactorMinimal second) hne) firstElement.property)
          (secondElement : subgroup) secondElement.property).symm
    let productHom := MonoidHom.noncommPiCoprod
      (fun factor : factors => (factor : Subgroup subgroup).subtype) hfactorComm
    have hfamilyAmbient : generated ≤
        (⨆ factor : factors, (factor : Subgroup subgroup)).map subgroup.subtype := by
      apply iSup_le
      intro element
      exact Subgroup.map_mono (le_iSup (fun factor : factors =>
        (factor : Subgroup subgroup)) ⟨conjugate element, ⟨element, rfl⟩⟩)
    have hfamilyTop : (⨆ factor : factors, (factor : Subgroup subgroup)) = ⊤ := by
      apply top_unique
      intro element _
      have hmember : (element : source) ∈ generated := by
        rw [hgeneratedEq]
        exact element.property
      obtain ⟨lift, hlift, hequal⟩ := hfamilyAmbient hmember
      exact (Subtype.ext hequal : lift = element) ▸ hlift
    have hproductTop : productHom.range = ⊤ := by
      rw [MonoidHom.noncommPiCoprod_range]
      simpa only [Subgroup.range_subtype] using hfamilyTop
    have hcardDivides : Nat.card subgroup ∣
        Nat.card ((factor : factors) → (factor : Subgroup subgroup)) := by
      have hrange := Subgroup.card_range_dvd productHom
      rwa [hproductTop, Subgroup.card_top] at hrange
    have hproductDivides := hdivides.trans hcardDivides
    rw [Nat.card_pi] at hproductDivides
    obtain ⟨factor, _, hfactorDivides⟩ :=
      (Prime.dvd_finsetProd_iff hprime.prime _).mp hproductDivides
    obtain ⟨element, hequal⟩ := factor.property
    have hfactorCard : Nat.card (factor : Subgroup subgroup) = Nat.card simple := by
      rw [← hequal]
      exact Subgroup.card_map_of_injective (conjugation element).injective
    exact hfactorCard ▸ hfactorDivides
  have hsimpleGroup : IsSimpleGroup simple := by
    constructor
    intro normal hnormal
    let : normal.Normal := hnormal
    let normalAmbient := normal.map simple.subtype
    have hnormalContained : normalAmbient ≤ simple := Subgroup.map_subtype_le normal
    have hsimpleNormalizes : simple ≤ Subgroup.normalizer (normalAmbient : Set subgroup) := by
      have hnormalEq : normalAmbient.subgroupOf simple = normal :=
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective normal
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hnormalContained).mp
      rw [hnormalEq]
      infer_instance
    have hgeneratedNormalizes : generated ≤
        Subgroup.normalizer (normalAmbient.map subgroup.subtype : Set source) := by
      apply iSup_le
      intro element
      have hconjugateNormalizes : conjugate element ≤
          Subgroup.normalizer (normalAmbient : Set subgroup) := by
        by_cases hequal : conjugate element = simple
        · rw [hequal]
          exact hsimpleNormalizes
        · exact ((distinct_minimal_normal_subgroups_commute (conjugate element) simple
            (hconjugateMinimal element) hsimpleMinimal hequal).trans
              (Subgroup.centralizer_le hnormalContained)).trans (Subgroup.centralizer_le_normalizer _)
      exact (Subgroup.map_mono hconjugateNormalizes).trans (by
        intro member hmember
        exact Subgroup.le_normalizer_map subgroup.subtype hmember)
    have hnormalInSubgroup : normalAmbient.Normal := by
      refine ⟨?_⟩
      intro member hmember element
      have hscalar : (element : source) ∈
          Subgroup.normalizer (normalAmbient.map subgroup.subtype : Set source) := by
        apply hgeneratedNormalizes
        rw [hgeneratedEq]
        exact element.property
      have hconjugate := (Subgroup.mem_normalizer_iff.mp hscalar (member : source)).mp
        (Subgroup.mem_map_of_mem subgroup.subtype hmember)
      obtain ⟨lift, hlift, hequal⟩ := hconjugate
      exact (Subtype.ext hequal : lift = element * member * element⁻¹) ▸ hlift
    by_cases hbot : normalAmbient = ⊥
    · left
      apply Subgroup.map_injective (f := simple.subtype) Subtype.val_injective
      simpa only [Subgroup.map_bot] using hbot
    · right
      have hsimpleLe := hsimpleMinimal.2 ⟨hnormalInSubgroup, hbot⟩ hnormalContained
      apply top_unique
      intro element _
      obtain ⟨lift, hlift, hequal⟩ := hsimpleLe element.property
      exact (Subtype.ext hequal : lift = element) ▸ hlift
  refine ⟨simple, hsimpleMinimal, hsimpleGroup, ?_, hprimeTransfer⟩
  intro hcenter
  by_contra hnonab
  have hcommutative : ∀ first second : simple, first * second = second * first := by
    intro first second
    by_contra hnotCommute
    exact hnonab ⟨first, second, hnotCommute⟩
  have hsimpleCentral : simple ≤ Subgroup.centralizer (simple : Set subgroup) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (IsMulCommutative.of_comm hcommutative)
  have hgeneratedCentral : generated ≤
      Subgroup.centralizer (simple.map subgroup.subtype : Set source) := by
    apply iSup_le
    intro element
    have hconjugateCentral : conjugate element ≤ Subgroup.centralizer (simple : Set subgroup) := by
      by_cases hequal : conjugate element = simple
      · rw [hequal]
        exact hsimpleCentral
      · exact distinct_minimal_normal_subgroups_commute (conjugate element) simple
          (hconjugateMinimal element) hsimpleMinimal hequal
    rintro member ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro other ⟨otherLift, hother, rfl⟩
    exact congrArg (fun value : subgroup => (value : source))
      (Subgroup.mem_centralizer_iff.mp (hconjugateCentral hlift) otherLift hother)
  have hsimpleCenter : simple ≤ Subgroup.center subgroup := by
    intro member hmember
    apply Subgroup.mem_center_iff.mpr
    intro element
    have helementCentral : (element : source) ∈
        Subgroup.centralizer (simple.map subgroup.subtype : Set source) := by
      apply hgeneratedCentral
      rw [hgeneratedEq]
      exact element.property
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp helementCentral (member : source)
      (Subgroup.mem_map_of_mem subgroup.subtype hmember)).symm
  exact hsimpleMinimal.1.2 (bot_unique (hcenter ▸ hsimpleCenter))


end CFSG.PreuniquenessRankFour.Helpers
