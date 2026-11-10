module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction

public section

open CFSG.Open
open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem nonzero_vector_has_surjective_additive_functional
    {coefficient : Type u} {space : Type v}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    (member : space) (hnonzero : member ≠ 0) :
    ∃ hom : space →+ coefficient, hom member = 1 ∧ Function.Surjective hom := by
  obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_eq_one coefficient hnonzero
  refine ⟨functional.toAddMonoidHom, hfunctional, ?_⟩
  intro value
  refine ⟨value • member, ?_⟩
  change functional (value • member) = value
  rw [map_smul, hfunctional, smul_eq_mul, mul_one]

theorem prime_card_group_frattini_eq_bot
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hcard : Nat.card source = prime) :
    frattini source = ⊥ := by
  let : Fact (Nat.card source).Prime := ⟨hcard ▸ Fact.out⟩
  have hbotCoatom : IsCoatom (⊥ : Subgroup source) := by
    refine ⟨?_, ?_⟩
    · intro hequal
      have hcards := congrArg (fun subgroup : Subgroup source => Nat.card subgroup) hequal
      rw [Subgroup.card_bot, Subgroup.card_top, hcard] at hcards
      exact (Fact.out : prime.Prime).ne_one hcards.symm
    · intro subgroup hlarge
      exact (subgroup.eq_bot_or_eq_top_of_prime_card).resolve_left (ne_of_gt hlarge)
  exact bot_unique (frattini_le_coatom hbotCoatom)

theorem elementary_group_frattini_eq_bot
    {source : Type u} [CommGroup source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hpow : ∀ member : source, member ^ prime = 1) :
    frattini source = ⊥ := by
  let : Module (ZMod prime) (Additive source) :=
    AddCommGroup.zmodModule (n := prime) (G := Additive source) fun member => by
    change Additive.ofMul (member.toMul ^ prime) = 0
    rw [hpow]
    rfl
  apply (Subgroup.eq_bot_iff_forall (frattini source)).mpr
  intro member hmember
  by_contra hnonidentity
  have hnonzero : (Additive.ofMul member : Additive source) ≠ 0 := hnonidentity
  obtain ⟨functional, hfunctional, hfunctionalSurjective⟩ :=
    nonzero_vector_has_surjective_additive_functional (coefficient := ZMod prime)
      (Additive.ofMul member) hnonzero
  let hom : source →* Multiplicative (ZMod prime) :=
    { toFun := fun element => Multiplicative.ofAdd (functional (Additive.ofMul element))
      map_one' := by exact congrArg Multiplicative.ofAdd functional.map_zero
      map_mul' := fun first second => congrArg Multiplicative.ofAdd
        (functional.map_add (Additive.ofMul first) (Additive.ofMul second)) }
  have hsurjective : Function.Surjective hom := by
    intro value
    obtain ⟨lift, hlift⟩ := hfunctionalSurjective value.toAdd
    exact ⟨lift.toMul, congrArg Multiplicative.ofAdd hlift⟩
  have hfrattini := frattini_le_comap_frattini_of_surjective hsurjective hmember
  rw [prime_card_group_frattini_eq_bot prime (by simp)] at hfrattini
  have hzero : functional (Additive.ofMul member) = 0 := Subgroup.mem_bot.mp hfrattini
  rw [hfunctional] at hzero
  exact one_ne_zero hzero

theorem frattini_le_normal_of_elementary_quotient
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (normal : Subgroup source) [normal.Normal]
    (helementary : IsElemAbelian prime (⊤ : Subgroup (source ⧸ normal))) :
    frattini source ≤ normal := by
  let : IsMulCommutative (source ⧸ normal) := IsMulCommutative.of_comm fun first second =>
    congrArg Subtype.val ((isMulCommutative_iff.mp helementary.1)
      (⟨first, Subgroup.mem_top _⟩ : (⊤ : Subgroup (source ⧸ normal)))
      ⟨second, Subgroup.mem_top _⟩)
  let : CommGroup (source ⧸ normal) := IsMulCommutative.instCommGroup
  have hfrattini : frattini (source ⧸ normal) = ⊥ := elementary_group_frattini_eq_bot prime
    (fun member => helementary.2 member (Subgroup.mem_top member))
  have hcontained := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective normal)
  rw [hfrattini, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hcontained
  exact hcontained

theorem pGroup_normal_subgroup_meets_center
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnontrivial : normal ≠ ⊥) :
    normal ⊓ Subgroup.center source ≠ ⊥ := by
  let : Nontrivial normal := normal.nontrivial_iff_ne_bot.mpr hnontrivial
  let : MulDistribMulAction source normal :=
    MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
  have hnormalGroup : IsPGroup prime normal := hgroup.to_subgroup normal
  have hcard : prime ∣ Nat.card normal := hnormalGroup.card_eq_or_dvd.resolve_left
    (fun hcardOne => hnontrivial (normal.eq_bot_iff_card.mpr hcardOne))
  have hfixedOne : (1 : normal) ∈ MulAction.fixedPoints source normal := fun scalar => smul_one scalar
  obtain ⟨member, hfixed, hnonidentity⟩ :=
    hgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point normal hcard hfixedOne
  intro hbot
  have hcentral : (member : source) ∈ Subgroup.center source := by
    apply Subgroup.mem_center_iff.mpr
    intro scalar
    have hequal := congrArg Subtype.val (hfixed scalar)
    change scalar * (member : source) * scalar⁻¹ = member at hequal
    have hcommute := congrArg (fun value : source => value * scalar) hequal
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute
  have hidentity := Subgroup.mem_bot.mp
    (hbot ▸ (show (member : source) ∈ normal ⊓ Subgroup.center source from ⟨member.property, hcentral⟩))
  exact hnonidentity (Subtype.ext hidentity.symm)

@[expose] noncomputable def centralPrimeTorsion (prime : ℕ) (source : Type u) [Group source] : Subgroup source :=
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  ((powMonoidHom prime : Subgroup.center source →* Subgroup.center source).ker).map
    (Subgroup.center source).subtype

theorem mem_centralPrimeTorsion
    {source : Type u} [Group source] (prime : ℕ) (member : source) :
    member ∈ centralPrimeTorsion prime source ↔
      member ∈ Subgroup.center source ∧ member ^ prime = 1 := by
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    exact ⟨lift.property, congrArg Subtype.val hlift⟩
  · rintro ⟨hcentral, hpow⟩
    exact ⟨⟨member, hcentral⟩, Subtype.ext hpow, rfl⟩

theorem centralPrimeTorsion_characteristic
    {source : Type u} [Group source] (prime : ℕ) :
    (centralPrimeTorsion prime source).Characteristic := by
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  let : (powMonoidHom prime : Subgroup.center source →* Subgroup.center source).ker.Characteristic :=
    power_kernel_characteristic prime
  exact Subgroup.characteristic_of_characteristic_of_characteristic

theorem centralPrimeTorsion_elementary
    {source : Type u} [Group source] (prime : ℕ) :
    IsElemAbelian prime (centralPrimeTorsion prime source) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro first second
    apply Subtype.ext
    change (first : source) * (second : source) = (second : source) * (first : source)
    exact (Subgroup.mem_center_iff.mp
      ((mem_centralPrimeTorsion prime (first : source)).mp first.property).1 (second : source)).symm
  · intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).2

theorem pGroup_normal_subgroup_meets_centralPrimeTorsion
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnontrivial : normal ≠ ⊥) :
    normal ⊓ centralPrimeTorsion prime source ≠ ⊥ := by
  let intersection := normal ⊓ Subgroup.center source
  have hnontrivialIntersection : intersection ≠ ⊥ :=
    pGroup_normal_subgroup_meets_center prime hgroup normal hnontrivial
  have hintersectionGroup : IsPGroup prime intersection := hgroup.to_subgroup intersection
  have hcard : prime ∣ Nat.card intersection := hintersectionGroup.card_eq_or_dvd.resolve_left
    (fun hcardOne => hnontrivialIntersection (intersection.eq_bot_iff_card.mpr hcardOne))
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' prime hcard
  have hpow : (member : source) ^ prime = 1 := by
    exact congrArg Subtype.val (horder ▸ pow_orderOf_eq_one member)
  intro hbot
  have hidentity : (member : source) = 1 := Subgroup.mem_bot.mp
    (hbot ▸ (show (member : source) ∈ normal ⊓ centralPrimeTorsion prime source from
      ⟨member.property.1, (mem_centralPrimeTorsion prime (member : source)).mpr
        ⟨member.property.2, hpow⟩⟩))
  have hmemberIdentity : member = 1 := Subtype.ext hidentity
  rw [hmemberIdentity, orderOf_one] at horder
  exact (Fact.out : prime.Prime).ne_one horder.symm

theorem subgroup_center_image_eq_inf_centralizer
    {source : Type u} [Group source] (subgroup : Subgroup source) :
    (Subgroup.center subgroup).map subgroup.subtype =
      subgroup ⊓ Subgroup.centralizer (subgroup : Set source) := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    refine ⟨lift.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro other hother
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hlift (⟨other, hother⟩ : subgroup))
  · rintro ⟨hmember, hcentral⟩
    refine ⟨⟨member, hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcentral other other.property

theorem subgroup_quotient_map_le_center_of_commutator_le
    {source : Type u} [Group source] (normal subgroup : Subgroup source) [normal.Normal]
    (hcommutator : ⁅(⊤ : Subgroup source), subgroup⁆ ≤ normal) :
    subgroup.map (QuotientGroup.mk' normal) ≤ Subgroup.center (source ⧸ normal) := by
  rintro member ⟨lift, hlift, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro other
  obtain ⟨otherLift, rfl⟩ := QuotientGroup.mk'_surjective normal other
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top otherLift) hlift))

theorem subgroup_commutator_le_of_quotient_map_le_center
    {source : Type u} [Group source] (normal subgroup : Subgroup source) [normal.Normal]
    (hcentral : subgroup.map (QuotientGroup.mk' normal) ≤ Subgroup.center (source ⧸ normal)) :
    ⁅(⊤ : Subgroup source), subgroup⁆ ≤ normal := by
  apply Subgroup.commutator_le.mpr
  intro first _ second hsecond
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' normal) ⁅first, second⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact Subgroup.mem_center_iff.mp
    (hcentral (Subgroup.mem_map_of_mem _ hsecond)) ((QuotientGroup.mk' normal) first)

theorem pGroup_has_characteristic_critical_subgroup
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source) :
    ∃ critical : Subgroup source, critical.Characteristic ∧
      (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
      ⁅(⊤ : Subgroup source), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
      Subgroup.centralizer (critical : Set source) = (Subgroup.center critical).map critical.subtype := by
  classical
  let admissible := fun subgroup : Subgroup source => subgroup.Characteristic ∧
    (∀ member ∈ subgroup, member ^ prime ∈ (Subgroup.center subgroup).map subgroup.subtype) ∧
      ⁅(⊤ : Subgroup source), subgroup⁆ ≤ (Subgroup.center subgroup).map subgroup.subtype
  have hbot : admissible ⊥ := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro member hmember
      rw [Subgroup.mem_bot.mp hmember, one_pow]
      exact Subgroup.one_mem _
    · simp
  obtain ⟨critical, _, hmaximal⟩ := Finite.exists_le_maximal hbot
  let : critical.Characteristic := hmaximal.1.1
  let center := (Subgroup.center critical).map critical.subtype
  let centralizer := Subgroup.centralizer (critical : Set source)
  let : center.Characteristic := Subgroup.characteristic_of_characteristic_of_characteristic
  let : centralizer.Characteristic := inferInstance
  let quotientHom := QuotientGroup.mk' center
  have hcenterCritical : center ≤ critical := Subgroup.map_subtype_le _
  have hcriticalCentralizer : critical ⊓ centralizer = center :=
    (subgroup_center_image_eq_inf_centralizer critical).symm
  have hcenterCentralizer : center ≤ centralizer := by rw [← hcriticalCentralizer]; exact inf_le_right
  have hcriticalImageCentral : critical.map quotientHom ≤ Subgroup.center (source ⧸ center) :=
    subgroup_quotient_map_le_center_of_commutator_le center critical hmaximal.1.2.2
  have hcriticalImageElementary : IsElemAbelian prime (critical.map quotientHom) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro first second
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hcriticalImageCentral first.property) second).symm
    · rintro member ⟨lift, hlift, rfl⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hmaximal.1.2.1 lift hlift)
  have hcentralizerEq : centralizer = center := by
    by_contra hneq
    have himageNontrivial : centralizer.map quotientHom ≠ ⊥ := by
      intro hbotImage
      have hcontained : centralizer ≤ center := by
        have hkernel := (centralizer.map_eq_bot_iff).mp hbotImage
        rwa [QuotientGroup.ker_mk'] at hkernel
      exact hneq (le_antisymm hcontained hcenterCentralizer)
    let : (centralizer.map quotientHom).Normal :=
      (inferInstance : centralizer.Normal).map quotientHom (QuotientGroup.mk'_surjective center)
    let torsion := centralPrimeTorsion prime (source ⧸ center)
    let extension := centralizer ⊓ torsion.comap quotientHom
    let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
    let : (torsion.comap quotientHom).Characteristic :=
      Subgroup.Characteristic.comap_quotient_mk (inferInstance : torsion.Characteristic)
    let : extension.Characteristic := inferInstance
    have hcenterExtension : center ≤ extension := by
      refine le_inf hcenterCentralizer ?_
      intro member hmember
      change quotientHom member ∈ torsion
      have hquotientOne : quotientHom member = 1 := (QuotientGroup.eq_one_iff member).mpr hmember
      rw [hquotientOne]
      exact torsion.one_mem
    have hextensionNontrivial : ¬ extension ≤ center := by
      have hnontrivial := pGroup_normal_subgroup_meets_centralPrimeTorsion prime
        (hgroup.to_quotient center) (centralizer.map quotientHom) himageNontrivial
      intro hcontained
      apply hnontrivial
      apply (Subgroup.eq_bot_iff_forall _).mpr
      rintro member ⟨⟨lift, hlift, rfl⟩, htorsion⟩
      exact (QuotientGroup.eq_one_iff lift).mpr (hcontained ⟨hlift, htorsion⟩)
    have hextensionCentral : extension ≤ centralizer := inf_le_left
    have hextensionImage : extension.map quotientHom ≤ torsion :=
      Subgroup.map_le_iff_le_comap.mpr inf_le_right
    have hextensionImageCentral : extension.map quotientHom ≤ Subgroup.center (source ⧸ center) := by
      intro member hmember
      exact ((mem_centralPrimeTorsion prime member).mp (hextensionImage hmember)).1
    have hextensionImageElementary : IsElemAbelian prime (extension.map quotientHom) := by
      have helementary := centralPrimeTorsion_elementary (source := source ⧸ center) prime
      refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
      · intro first second
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hextensionImageCentral first.property) second).symm
      · intro member hmember
        exact helementary.2 member (hextensionImage hmember)
    let larger := critical ⊔ extension
    let : larger.Characteristic := inferInstance
    have hcenterLarger : center ≤ larger := hcenterCritical.trans le_sup_left
    have hcenterLargerCentral : center ≤ (Subgroup.center larger).map larger.subtype := by
      rw [subgroup_center_image_eq_inf_centralizer]
      refine le_inf hcenterLarger ?_
      apply Subgroup.le_centralizer_iff.mpr
      apply sup_le
      · exact Subgroup.le_centralizer_iff.mp hcenterCentralizer
      · exact hextensionCentral.trans (Subgroup.centralizer_le
          (show (center : Set source) ⊆ (critical : Set source) from hcenterCritical))
    have hlargerImageCentral : larger.map quotientHom ≤ Subgroup.center (source ⧸ center) := by
      rw [Subgroup.map_sup]
      exact sup_le hcriticalImageCentral hextensionImageCentral
    have hlargerImageElementary : IsElemAbelian prime (larger.map quotientHom) := by
      rw [Subgroup.map_sup]
      exact elementary_abelian_sup_of_commuting prime hcriticalImageElementary hextensionImageElementary
        (Subgroup.le_centralizer_iff.mpr (hextensionImageCentral.trans (Subgroup.center_le_centralizer _)))
    have hlargerAdmissible : admissible larger := by
      refine ⟨inferInstance, ?_, ?_⟩
      · intro member hmember
        apply hcenterLargerCentral
        apply (QuotientGroup.eq_one_iff _).mp
        change quotientHom (member ^ prime) = 1
        rw [map_pow]
        exact hlargerImageElementary.2 _ (Subgroup.mem_map_of_mem _ hmember)
      · exact (subgroup_commutator_le_of_quotient_map_le_center center larger hlargerImageCentral).trans
          hcenterLargerCentral
    have hlargerLe : larger ≤ critical := hmaximal.2 hlargerAdmissible le_sup_left
    have hextensionCritical : extension ≤ critical := le_sup_right.trans hlargerLe
    apply hextensionNontrivial
    rw [← hcriticalCentralizer]
    exact le_inf hextensionCritical hextensionCentral
  refine ⟨critical, inferInstance, ?_, hmaximal.1.2.2, hcentralizerEq⟩
  let centerLocal := center.subgroupOf critical
  have hcenterLocalEq : centerLocal = Subgroup.center critical :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hcommutatorLocal : commutator critical ≤ centerLocal := by
    apply (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp
    rw [map_commutator_eq, critical.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hcenterCritical]
    exact (Subgroup.commutator_mono le_top le_rfl).trans hmaximal.1.2.2
  let : IsMulCommutative (critical ⧸ centerLocal) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutatorLocal
  have hquotientElementary : IsElemAbelian prime (⊤ : Subgroup (critical ⧸ centerLocal)) := by
    refine ⟨inferInstance, ?_⟩
    intro member _
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective centerLocal member
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hmaximal.1.2.1 lift lift.property)
  exact Subgroup.map_le_iff_le_comap.mpr (frattini_le_normal_of_elementary_quotient prime centerLocal
    hquotientElementary)


@[expose, instance_reducible]
noncomputable def characteristic_subgroup_mulDistribMulAction
    {acting : Type u} {source : Type v} [Group acting] [Group source]
    [MulDistribMulAction acting source] (subgroup : Subgroup source) [subgroup.Characteristic] :
    MulDistribMulAction acting subgroup where
  smul scalar member := ⟨scalar • (member : source),
    (Subgroup.characteristic_iff_map_le.mp (inferInstance : subgroup.Characteristic)
      (MulDistribMulAction.toMulEquiv source scalar))
        (Subgroup.mem_map_of_mem _ member.property)⟩
  one_smul member := Subtype.ext (one_smul acting (member : source))
  mul_smul first second member := Subtype.ext (mul_smul first second (member : source))
  smul_one scalar := Subtype.ext (smul_one scalar)
  smul_mul scalar first second := Subtype.ext (smul_mul' scalar (first : source) (second : source))


theorem centralPrimeTorsion_card_eq_prime_of_cyclic_center
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hcenter : IsCyclic (Subgroup.center source)) (hnontrivial : Nontrivial source) :
    Nat.card (centralPrimeTorsion prime source) = prime := by
  let : Nontrivial source := hnontrivial
  let : IsCyclic (Subgroup.center source) := hcenter
  have htorsionCenter : centralPrimeTorsion prime source ≤ Subgroup.center source := by
    intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).1
  let : IsCyclic (centralPrimeTorsion prime source) := Subgroup.isCyclic_of_le htorsionCenter
  have htorsionPow : ∀ member : centralPrimeTorsion prime source, member ^ prime = 1 := by
    intro member
    apply Subtype.ext
    exact ((mem_centralPrimeTorsion prime (member : source)).mp member.property).2
  have hcard := cyclic_group_of_prime_exponent_card_eq_one_or_prime prime htorsionPow
  apply hcard.resolve_left
  intro hcardOne
  have hnontrivialTop : (⊤ : Subgroup source) ≠ ⊥ := top_ne_bot
  have hnontrivialTorsion := pGroup_normal_subgroup_meets_centralPrimeTorsion
    prime hsource ⊤ hnontrivialTop
  apply hnontrivialTorsion
  rw [top_inf_eq]
  exact (centralPrimeTorsion prime source).eq_bot_iff_card.mpr hcardOne


theorem class_two_center_quotient_commutator_pairing
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source) :
    letI : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
    ∃ pairing : (source ⧸ Subgroup.center source) →*
        (source ⧸ Subgroup.center source) →* Subgroup.center source,
      (∀ first second : source,
        (pairing ((QuotientGroup.mk' (Subgroup.center source)) first)
          ((QuotientGroup.mk' (Subgroup.center source)) second) : source) = ⁅first, second⁆) ∧
      (∀ member : source ⧸ Subgroup.center source, pairing member member = 1) ∧
      (∀ member : source ⧸ Subgroup.center source,
        (∀ other : source ⧸ Subgroup.center source, pairing member other = 1) → member = 1) := by
  let : CommGroup (Subgroup.center source) := IsMulCommutative.instCommGroup
  have hcentral : ∀ first second : source, ⁅first, second⁆ ∈ Subgroup.center source :=
    fun first second => hcommutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second))
  have hconjugate : ∀ first second scalar : source, scalar * ⁅first, second⁆ * scalar⁻¹ = ⁅first, second⁆ := by
    intro first second scalar
    rw [Subgroup.mem_center_iff.mp (hcentral first second) scalar, mul_inv_cancel_right]
  let base : source →* source →* Subgroup.center source :=
    { toFun := fun first =>
        { toFun := fun second => ⟨⁅first, second⁆, hcentral first second⟩
          map_one' := by apply Subtype.ext; simp
          map_mul' := fun second third => by
            apply Subtype.ext
            change ⁅first, second * third⁆ = ⁅first, second⁆ * ⁅first, third⁆
            rw [commutatorElement_mul_right_eq_mul_conj]
            calc
              _ = ⁅first, second⁆ * (second * ⁅first, third⁆ * second⁻¹) := by group
              _ = _ := by rw [hconjugate] }
      map_one' := by apply MonoidHom.ext; intro second; apply Subtype.ext; simp
      map_mul' := fun first second => by
        apply MonoidHom.ext
        intro third
        apply Subtype.ext
        change ⁅first * second, third⁆ = ⁅first, third⁆ * ⁅second, third⁆
        rw [commutatorElement_mul_left_eq_conj_mul, hconjugate,
          Subgroup.mem_center_iff.mp (hcentral second third) ⁅first, third⁆] }
  have hrightKernel : ∀ first : source, Subgroup.center source ≤ (base first).ker := by
    intro first second hsecond
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact Subgroup.mem_center_iff.mp hsecond first
  let rightLift : source →* (source ⧸ Subgroup.center source) →* Subgroup.center source :=
    { toFun := fun first => QuotientGroup.lift (Subgroup.center source) (base first) (hrightKernel first)
      map_one' := by
        apply MonoidHom.ext
        intro second
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
        change (QuotientGroup.lift (Subgroup.center source) (base 1) (hrightKernel 1))
          ((QuotientGroup.mk' (Subgroup.center source)) lift) = 1
        exact (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel 1) lift).trans
          (by rw [map_one, MonoidHom.one_apply])
      map_mul' := fun first second => by
        apply MonoidHom.ext
        intro third
        obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) third
        change (QuotientGroup.lift (Subgroup.center source) (base (first * second))
          (hrightKernel (first * second))) ((QuotientGroup.mk' (Subgroup.center source)) lift) =
          (QuotientGroup.lift (Subgroup.center source) (base first) (hrightKernel first))
            ((QuotientGroup.mk' (Subgroup.center source)) lift) *
          (QuotientGroup.lift (Subgroup.center source) (base second) (hrightKernel second))
            ((QuotientGroup.mk' (Subgroup.center source)) lift)
        exact (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel (first * second)) lift).trans
          ((by rw [map_mul, MonoidHom.mul_apply] : base (first * second) lift =
            base first lift * base second lift).trans (congrArg₂ (fun first second : Subgroup.center source =>
              first * second)
              (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel first) lift).symm
              (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel second) lift).symm)) }
  have hleftKernel : Subgroup.center source ≤ rightLift.ker := by
    intro first hfirst
    apply MonoidHom.ext
    intro second
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) second
    change (QuotientGroup.lift (Subgroup.center source) (base first) (hrightKernel first))
      ((QuotientGroup.mk' (Subgroup.center source)) lift) = 1
    apply (QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel first) lift).trans
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hfirst lift).symm
  let pairing := QuotientGroup.lift (Subgroup.center source) rightLift hleftKernel
  have hpairing : ∀ first second : source,
      (pairing ((QuotientGroup.mk' (Subgroup.center source)) first)
        ((QuotientGroup.mk' (Subgroup.center source)) second) : source) = ⁅first, second⁆ := by
    intro first second
    have hleft : pairing ((QuotientGroup.mk' (Subgroup.center source)) first) = rightLift first :=
      QuotientGroup.lift_mk' (Subgroup.center source) hleftKernel first
    have hright : rightLift first ((QuotientGroup.mk' (Subgroup.center source)) second) = base first second :=
      QuotientGroup.lift_mk' (Subgroup.center source) (hrightKernel first) second
    rw [hleft, hright]
    rfl
  refine ⟨pairing, hpairing, ?_, ?_⟩
  · intro member
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) member
    apply Subtype.ext
    rw [hpairing, commutatorElement_self]
    rfl
  · intro member hradical
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center source) member
    apply (QuotientGroup.eq_one_iff lift).mpr
    apply Subgroup.mem_center_iff.mpr
    intro other
    have hequal := congrArg Subtype.val (hradical ((QuotientGroup.mk' (Subgroup.center source)) other))
    rw [hpairing] at hequal
    exact (commutatorElement_eq_one_iff_mul_comm.mp hequal).symm

theorem multiplicative_pairing_has_zmod_bilinear_map
    {source : Type u} {target : Type v} [CommGroup source] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] [Module (ZMod prime) (Additive target)]
    (pairing : source →* source →* target) :
    ∃ bilinear : Additive source →ₗ[ZMod prime] Additive source →ₗ[ZMod prime] Additive target,
      ∀ first second : source,
        bilinear (Additive.ofMul first) (Additive.ofMul second) = Additive.ofMul (pairing first second) := by
  let additive : Additive source →+ (Additive source →+ Additive target) :=
    { toFun := fun first => MonoidHom.toAdditive (pairing first.toMul)
      map_zero' := by
        apply AddMonoidHom.ext
        intro second
        change Additive.ofMul ((pairing 1) second.toMul) = 0
        rw [map_one, MonoidHom.one_apply]
        rfl
      map_add' := fun first second => by
        apply AddMonoidHom.ext
        intro third
        change Additive.ofMul ((pairing (first.toMul * second.toMul)) third.toMul) =
          Additive.ofMul (pairing first.toMul third.toMul) +
            Additive.ofMul (pairing second.toMul third.toMul)
        rw [map_mul, MonoidHom.mul_apply]
        rfl }
  let additiveLinear : Additive source →+ (Additive source →ₗ[ZMod prime] Additive target) :=
    (AddMonoidHom.toZModLinearMapEquiv prime).toAddMonoidHom.comp additive
  exact ⟨AddMonoidHom.toZModLinearMap prime additiveLinear, fun _ _ => rfl⟩


theorem prime_card_zmod_module_has_linear_equiv
    {space : Type u} [AddCommGroup space] [Finite space]
    (prime : ℕ) [Fact prime.Prime] [Module (ZMod prime) space]
    (hcard : Nat.card space = prime) :
    Nonempty (space ≃ₗ[ZMod prime] ZMod prime) := by
  let : Nontrivial space := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [hcard]; exact (Fact.out : prime.Prime).one_lt)
  obtain ⟨member, hnonzero⟩ := exists_ne (0 : space)
  obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_eq_one (ZMod prime) hnonzero
  have hsurjective : Function.Surjective functional := by
    intro value
    refine ⟨value • member, ?_⟩
    rw [map_smul, hfunctional, smul_eq_mul, mul_one]
  have hbijective : Function.Bijective functional :=
    (Nat.bijective_iff_surjective_and_card functional).mpr
      ⟨hsurjective, by simpa only [Nat.card_eq_fintype_card, ZMod.card] using hcard⟩
  exact ⟨LinearEquiv.ofBijective functional hbijective⟩

theorem multiplicative_pairing_has_nondegenerate_alternating_form
    {source : Type u} {target : Type v} [CommGroup source] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] [Module (ZMod prime) (Additive target)]
    (coordinate : Additive target ≃ₗ[ZMod prime] ZMod prime)
    (pairing : source →* source →* target)
    (halt : ∀ member : source, pairing member member = 1)
    (hradical : ∀ member : source, (∀ other : source, pairing member other = 1) → member = 1) :
    ∃ form : LinearMap.BilinForm (ZMod prime) (Additive source),
      form.IsAlt ∧ form.Nondegenerate ∧
        ∀ first second : source,
          form (Additive.ofMul first) (Additive.ofMul second) =
            coordinate (Additive.ofMul (pairing first second)) := by
  obtain ⟨bilinear, hbilinear⟩ := multiplicative_pairing_has_zmod_bilinear_map prime pairing
  let form : LinearMap.BilinForm (ZMod prime) (Additive source) :=
    ((LinearMap.llcomp (ZMod prime) (Additive source) (Additive target) (ZMod prime))
      coordinate.toLinearMap).comp bilinear
  have happly : ∀ first second : source,
      form (Additive.ofMul first) (Additive.ofMul second) =
        coordinate (Additive.ofMul (pairing first second)) := by
    intro first second
    change coordinate (bilinear (Additive.ofMul first) (Additive.ofMul second)) = _
    rw [hbilinear]
  have halternating : form.IsAlt := by
    intro member
    change form (Additive.ofMul member.toMul) (Additive.ofMul member.toMul) = 0
    rw [happly, halt]
    exact coordinate.map_zero
  have hleft : ∀ member : Additive source,
      (∀ other : Additive source, form member other = 0) → member = 0 := by
    intro member hfixed
    change member.toMul = 1
    apply hradical
    intro other
    have hequal := hfixed (Additive.ofMul other)
    change form (Additive.ofMul member.toMul) (Additive.ofMul other) = 0 at hequal
    rw [happly] at hequal
    exact coordinate.injective (hequal.trans coordinate.map_zero.symm)
  refine ⟨form, halternating, ⟨hleft, ?_⟩, happly⟩
  intro member hfixed
  apply hleft
  intro other
  exact halternating.eq_iff.mpr (hfixed other)


@[instance_reducible]
noncomputable def centralPrimeTorsion_zmod_module
    {source : Type u} [Group source] (prime : ℕ) :
    letI : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
    letI : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
    Module (ZMod prime) (Additive (centralPrimeTorsion prime source)) := by
  let : IsMulCommutative (centralPrimeTorsion prime source) := (centralPrimeTorsion_elementary prime).1
  let : CommGroup (centralPrimeTorsion prime source) := IsMulCommutative.instCommGroup
  exact AddCommGroup.zmodModule fun member => by
    change member.toMul ^ prime = 1
    apply Subtype.ext
    exact (centralPrimeTorsion_elementary (source := source) prime).2
      member.toMul member.toMul.property


theorem pGroup_composite_hom_kernel
    {first : Type u} {second : Type v} {third : Type*}
    [Group first] [Group second] [Group third]
    (prime : ℕ) (firstHom : first →* second) (secondHom : second →* third)
    (hfirstKernel : IsPGroup prime firstHom.ker) (hsecondKernel : IsPGroup prime secondHom.ker) :
    IsPGroup prime (secondHom.comp firstHom).ker := by
  exact hsecondKernel.comap_of_ker_isPGroup firstHom hfirstKernel


theorem selfcentralizing_normal_conjugation_action_kernel_isPGroup
    {ambient : Type u} [Group ambient]
    (prime : ℕ) (normal : Subgroup ambient) [normal.Normal]
    (hnormal : IsPGroup prime normal)
    (hcentralizer : Subgroup.centralizer (normal : Set ambient) ≤ normal) :
    letI : MulDistribMulAction ambient normal :=
      MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
    IsPGroup prime (MulDistribMulAction.toMulAut ambient normal).ker := by
  let : MulDistribMulAction ambient normal :=
    MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
  apply hnormal.to_le
  intro scalar hscalar
  apply hcentralizer
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hequal := congrArg (fun equivalence : MulAut normal => equivalence (⟨member, hmember⟩ : normal))
    (show MulDistribMulAction.toMulAut ambient normal scalar = 1 from hscalar)
  have hfixed := congrArg Subtype.val hequal
  change scalar * member * scalar⁻¹ = member at hfixed
  have hmultiplied := congrArg (fun value : ambient => value * scalar) hfixed
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmultiplied.symm


end CFSG.PreuniquenessRankFour.Helpers
