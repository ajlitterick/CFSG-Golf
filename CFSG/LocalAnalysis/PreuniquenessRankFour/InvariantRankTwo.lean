module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalRankTwo

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem odd_pGroup_normal_noncyclic_has_ambient_normal_elementary_rank_two
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (cardinality : ℕ) :
    ∀ {source : Type u} [Group source] [Finite source], IsPGroup prime source →
      ∀ normal : Subgroup source, normal.Normal → Nat.card normal = cardinality → ¬ IsCyclic normal →
        ∃ elementary : Subgroup source, elementary ≤ normal ∧ elementary.Normal ∧
          IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  induction cardinality using Nat.strong_induction_on with
  | h cardinality hinduction =>
    intro source _ _ hsource normal hnormal hcardinality hnoncyclic
    let : normal.Normal := hnormal
    classical
    by_contra hnone
    have hnoNormal : ∀ elementary : Subgroup source, elementary ≤ normal → elementary.Normal →
        IsElemAbelian prime elementary → Nat.card elementary ≠ prime ^ 2 := by
      intro elementary hcontained hnormal helementary hcard
      exact hnone ⟨elementary, hcontained, hnormal, helementary, hcard⟩
    have hnormalNontrivial : normal ≠ ⊥ := by
      intro hbot
      have htrivial : Subsingleton normal := by rw [hbot]; infer_instance
      let : Subsingleton normal := htrivial
      exact hnoncyclic inferInstance
    obtain ⟨line, hline, hlineCentral, hlineCard, hlineNormal⟩ :=
      normal_pSubgroup_has_central_prime_line prime hsource normal hnormalNontrivial
    let : line.Normal := hlineNormal
    let quotientMap := QuotientGroup.mk' line
    let image := normal.map quotientMap
    let : image.Normal := hnormal.map quotientMap (QuotientGroup.mk'_surjective line)
    have hpreimage : image.comap quotientMap = normal := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hline]
    have himageSmall : Nat.card image < cardinality := by
      have hproduct := surjective_hom_preimage_card quotientMap (QuotientGroup.mk'_surjective line) image
      rw [hpreimage, QuotientGroup.ker_mk', hlineCard, hcardinality] at hproduct
      have hpositive : 0 < Nat.card image := Nat.card_pos
      have hprime := (Fact.out : prime.Prime).one_lt
      nlinarith
    by_cases himageCyclic : IsCyclic image
    · let : IsCyclic image := himageCyclic
      let restriction := quotientMap.subgroupMap normal
      have hkernelCentral : restriction.ker ≤ Subgroup.center normal := by
        intro member hmember
        have hzero := congrArg (fun value : image => (value : source ⧸ line)) hmember
        have hmemberLine : (member : source) ∈ line := (QuotientGroup.eq_one_iff _).mp hzero
        apply Subgroup.mem_center_iff.mpr
        intro other
        exact Subtype.ext (Subgroup.mem_center_iff.mp (hlineCentral hmemberLine) (other : source))
      have hcommutative : IsMulCommutative normal :=
        restriction.isMulCommutative_of_isCyclic_of_ker_le_center hkernelCentral
      let : IsMulCommutative normal := hcommutative
      let : CommGroup normal := IsMulCommutative.instCommGroup
      let torsion := centralPrimeTorsion prime normal
      let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
      let torsionImage := torsion.map normal.subtype
      let : torsionImage.Normal := inferInstance
      have htorsionRank : 2 ≤ pRank prime torsionImage := by
        rw [pRank_map_of_injective prime (Fact.out : prime.Prime) normal.subtype Subtype.val_injective,
          centralPrimeTorsion_rank_eq_center_rank prime (Fact.out : prime.Prime), Subgroup.center_eq_top]
        exact noncyclic_commutative_pGroup_rank_at_least_two
          prime (Fact.out : prime.Prime) (hsource.to_subgroup normal) hnoncyclic
      have htorsionElementary := elementary_abelian_map prime (centralPrimeTorsion_elementary prime) normal.subtype
      obtain ⟨rank, htorsionCard⟩ := (hsource.to_subgroup torsionImage).exists_card_eq
      have hrank : 2 ≤ rank := by
        obtain ⟨attaining, hcontained, _, hattainingCard⟩ :=
          pRank_attained prime (Fact.out : prime.Prime) torsionImage
        have hbound := Subgroup.card_le_of_le hcontained
        rw [hattainingCard, htorsionCard] at hbound
        exact htorsionRank.trans ((Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound)
      obtain ⟨small, hsmall, hsmallNormal, hsmallElementary, hsmallCard⟩ :=
        normal_elementary_contains_ambient_normal_elementary_of_each_rank
          prime hsource torsionImage htorsionElementary rank htorsionCard 2 hrank
      exact hnoNormal small (hsmall.trans (Subgroup.map_subtype_le _)) hsmallNormal hsmallElementary hsmallCard
    · obtain ⟨quotientElementary, hquotientContained, hquotientNormal, hquotientElementary, hquotientCard⟩ :=
        hinduction _ himageSmall (hsource.to_quotient line) image
          (inferInstance : image.Normal) rfl himageCyclic
      let : quotientElementary.Normal := hquotientNormal
      let preimage := quotientElementary.comap quotientMap
      let : preimage.Normal := inferInstance
      have hcontained : preimage ≤ normal := hpreimage ▸ Subgroup.comap_mono hquotientContained
      have hpreimageCard : Nat.card preimage = prime ^ 3 := by
        rw [surjective_hom_preimage_card quotientMap (QuotientGroup.mk'_surjective line),
          QuotientGroup.ker_mk', hlineCard, hquotientCard]
        simp only [pow_succ]
      have hcommutator : ⁅preimage, preimage⁆ ≤ line := by
        apply Subgroup.commutator_le.mpr
        intro first hfirst second hsecond
        apply (QuotientGroup.eq_one_iff _).mp
        change quotientMap ⁅first, second⁆ = 1
        rw [map_commutatorElement]
        apply commutatorElement_eq_one_iff_mul_comm.mpr
        let : IsMulCommutative quotientElementary := hquotientElementary.1
        let : CommGroup quotientElementary := IsMulCommutative.instCommGroup
        exact congrArg (fun value : quotientElementary => (value : source ⧸ line))
          (mul_comm (⟨quotientMap first, hfirst⟩ : quotientElementary)
            (⟨quotientMap second, hsecond⟩ : quotientElementary))
      obtain ⟨small, hsmall, hsmallNormal, hsmallElementary, hsmallCard⟩ :=
        normal_prime_cube_elementary_central_extension_has_normal_elementary_rank_two
          prime hodd hsource preimage line hpreimageCard hlineCard hcommutator (by
            intro member hmember
            apply (QuotientGroup.eq_one_iff _).mp
            change quotientMap (member ^ prime) = 1
            rw [map_pow]
            exact hquotientElementary.2 _ hmember)
      exact hnoNormal small (hsmall.trans hcontained) hsmallNormal hsmallElementary hsmallCard

theorem odd_pGroup_invariant_noncyclic_pSubgroup_has_invariant_elementary_rank_two
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (acting normal : Subgroup source) (hacting : IsPGroup prime acting) (hnormal : IsPGroup prime normal)
    (hnormalized : acting ≤ Subgroup.normalizer (normal : Set source))
    (hnoncyclic : ¬ IsCyclic normal) :
    ∃ elementary : Subgroup source, elementary ≤ normal ∧
      acting ≤ Subgroup.normalizer (elementary : Set source) ∧
        IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  let joined := normal ⊔ acting
  have hjoined : IsPGroup prime joined := hnormal.to_sup_of_normal_left' hacting hnormalized
  have hnormalJoined : joined ≤ Subgroup.normalizer (normal : Set source) :=
    sup_le Subgroup.le_normalizer hnormalized
  let localNormal := normal.subgroupOf joined
  let : localNormal.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnormalJoined
  have hnoncyclicLocal : ¬ IsCyclic localNormal := by
    intro hcyclic
    exact hnoncyclic ((normal.subgroupOfEquivOfLe (le_sup_left : normal ≤ joined)).isCyclic.mp hcyclic)
  obtain ⟨localElementary, hcontained, hlocalNormal, hlocalElementary, hlocalCard⟩ :=
    odd_pGroup_normal_noncyclic_has_ambient_normal_elementary_rank_two
      prime hodd (Nat.card localNormal) hjoined localNormal
        (inferInstance : localNormal.Normal) rfl hnoncyclicLocal
  let mapped := localElementary.map joined.subtype
  have hmappedContained : mapped ≤ normal := by
    have hbound : localElementary.map joined.subtype ≤ localNormal.map joined.subtype :=
      Subgroup.map_mono hcontained
    rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : normal ≤ joined)] at hbound
    exact hbound
  have hmappedNormal : (mapped.subgroupOf joined).Normal := by
    change ((localElementary.map joined.subtype).comap joined.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    exact hlocalNormal
  have hnormalizer : joined ≤ Subgroup.normalizer (mapped : Set source) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le localElementary)).mp hmappedNormal
  refine ⟨mapped, hmappedContained, (le_sup_right : acting ≤ joined).trans hnormalizer,
    elementary_abelian_map prime hlocalElementary joined.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  exact hlocalCard


theorem normal_elementary_rank_two_pGroup_centralizer_rank_eq
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnormal : IsElemAbelian prime normal)
    (hcard : Nat.card normal = prime ^ 2) :
    pRank prime (Subgroup.centralizer (normal : Set source)) = pRank prime (⊤ : Subgroup source) := by
  apply le_antisymm (pRank_mono prime (Fact.out : prime.Prime) le_top)
  obtain ⟨elementary, _, helementary, helementaryCard⟩ :=
    pRank_attained prime (Fact.out : prime.Prime) (⊤ : Subgroup source)
  let rank := pRank prime (⊤ : Subgroup source)
  have hrank : 2 ≤ rank := le_csSup (pRank_bddAbove prime (Fact.out : prime.Prime) _)
    ⟨normal, le_top, hnormal, hcard⟩
  let : IsMulCommutative normal := hnormal.1
  let : CommGroup normal := IsMulCommutative.instCommGroup
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  let actionHom := normal.normalizerMonoidHom.comp
    (Subgroup.inclusion (show elementary ≤ Subgroup.normalizer (normal : Set source) from by
      rw [Subgroup.normalizer_eq_top]; exact le_top))
  let : MulDistribMulAction elementary normal := MulDistribMulAction.compHom normal actionHom
  obtain ⟨kernel, hindex, hfixed⟩ := pGroup_action_on_elementary_rank_two_has_prime_index_kernel
    prime (hsource.to_subgroup elementary) hcard
      (fun member => Subtype.ext (hnormal.2 member member.property))
  let kernelAmbient := kernel.map elementary.subtype
  have hkernelElementary : IsElemAbelian prime kernelAmbient :=
    elementary_abelian_map prime ⟨inferInstance, fun member hmember =>
      Subtype.ext (helementary.2 member member.property)⟩ elementary.subtype
  have hkernelCentral : kernelAmbient ≤ Subgroup.centralizer (normal : Set source) := by
    rintro member ⟨scalar, hscalar, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hequal := congrArg (fun value : normal => (value : source))
      (hfixed scalar hscalar (⟨other, hother⟩ : normal))
    change (scalar : source) * other * (scalar : source)⁻¹ = other at hequal
    exact (mul_inv_eq_iff_eq_mul.mp hequal).symm
  have hkernelRank : rank - 1 ≤ pRank prime kernelAmbient :=
    elementary_prime_index_subgroup_rank prime (Fact.out : prime.Prime)
      helementary rank helementaryCard kernel hindex
  let joined := normal ⊔ kernelAmbient
  have hjoinedElementary : IsElemAbelian prime joined :=
    elementary_abelian_sup_of_commuting prime hnormal hkernelElementary
      (Subgroup.le_centralizer_iff.mp hkernelCentral)
  have hjoinedCentral : joined ≤ Subgroup.centralizer (normal : Set source) :=
    sup_le (Subgroup.le_centralizer normal) hkernelCentral
  by_cases hjoinedRank : rank ≤ pRank prime joined
  · exact hjoinedRank.trans (pRank_mono prime (Fact.out : prime.Prime) hjoinedCentral)
  · obtain ⟨kernelRank, hkernelCard⟩ := (hsource.to_subgroup kernelAmbient).exists_card_eq
    have hkernelRankLower : rank - 1 ≤ kernelRank := by
      obtain ⟨attaining, hcontained, _, hattainingCard⟩ :=
        pRank_attained prime (Fact.out : prime.Prime) kernelAmbient
      have hbound := Subgroup.card_le_of_le hcontained
      rw [hattainingCard, hkernelCard] at hbound
      exact hkernelRank.trans ((Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound)
    have hequal : kernelAmbient = joined := elementary_subgroup_eq_of_rank_bound
      prime (Fact.out : prime.Prime) hjoinedElementary le_sup_right kernelRank hkernelCard (by omega)
    have hnormalKernel : normal ≤ kernelAmbient := hequal ▸ (le_sup_left : normal ≤ joined)
    have hnormalElementary : normal ≤ elementary := hnormalKernel.trans (Subgroup.map_subtype_le kernel)
    have hcentral := commutative_subgroup_le_centralizer helementary.1 hnormalElementary
    exact le_csSup (pRank_bddAbove prime (Fact.out : prime.Prime) _)
      ⟨elementary, hcentral, helementary, helementaryCard⟩


end CFSG.PreuniquenessRankFour.Helpers
