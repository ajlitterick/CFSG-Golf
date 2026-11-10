module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeSylowTransitivity

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

universe u

@[expose] def coprimeActionTraceHom
    {Actor Value : Type*} [Group Actor] [Fintype Actor] [AddCommGroup Value]
    [DistribMulAction Actor Value] : Value →+ Value where
  toFun := coprimeActionTrace (Actor := Actor)
  map_zero' := by
    simp [coprimeActionTrace]
  map_add' := by
    intro first second
    simp only [coprimeActionTrace, smul_add, Finset.sum_add_distrib]

theorem coprimeActionTrace_smul_input
    {Actor Value : Type*} [Group Actor] [Fintype Actor] [AddCommGroup Value]
    [DistribMulAction Actor Value] (actingElement : Actor) (element : Value) :
    coprimeActionTrace (Actor := Actor) (actingElement • element) =
      coprimeActionTrace (Actor := Actor) element := by
  unfold coprimeActionTrace
  exact Fintype.sum_equiv (Equiv.mulRight actingElement)
    (fun other => other • actingElement • element) (fun other => other • element)
    (fun other => (mul_smul other actingElement element).symm)

theorem abelian_pGroup_trace_fixed_order_prime_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (htraceCommute : ∀ actingElement : Actor, ∀ element : Value,
      coprimeActionTrace (Actor := OtherActor) (actingElement • element) =
        actingElement • coprimeActionTrace (Actor := OtherActor) element)
    (hcentralizes : ∀ element : Value, prime • element = 0 →
      (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  let : Fact prime.Prime := ⟨hprime⟩
  let trace := coprimeActionTraceHom (Actor := OtherActor) (Value := Value)
  let traceKernel := trace.ker
  have htraceCommuteHom (actingElement : Actor) (element : Value) :
      trace (actingElement • element) = actingElement • trace element :=
    htraceCommute actingElement element
  let : DistribMulAction Actor traceKernel := {
    smul := fun actingElement element => ⟨actingElement • (element : Value), by
      change trace (actingElement • (element : Value)) = 0
      rw [htraceCommuteHom, element.property, smul_zero]⟩
    one_smul := by
      intro element
      apply Subtype.ext
      exact one_smul _ _
    mul_smul := by
      intro first second element
      apply Subtype.ext
      exact mul_smul _ _ _
    smul_zero := by
      intro actingElement
      apply Subtype.ext
      exact smul_zero _
    smul_add := by
      intro actingElement first second
      apply Subtype.ext
      exact smul_add _ _ _ }
  have hkernelPGroup : IsPGroup prime (Multiplicative traceKernel) := by
    have hexponent := isPGroup_iff_pow_pow_eq_one.mp hvalue
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro element
    obtain ⟨exponent, hpower⟩ := hexponent
      (Multiplicative.ofAdd ((Multiplicative.toAdd element : traceKernel) : Value))
    refine ⟨exponent, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hpower
  have hkernelFixedZero (element : traceKernel)
      (hkilled : prime • element = 0)
      (hfixed : ∀ actingElement : Actor, actingElement • element = element) : element = 0 := by
    apply Subtype.ext
    apply (nsmulCoprime hcoprime).injective
    rw [nsmulCoprime_apply, nsmulCoprime_apply, AddSubgroup.coe_zero, nsmul_zero]
    have hotherFixed := hcentralizes (element : Value) (congrArg Subtype.val hkilled)
      (fun actingElement => congrArg Subtype.val (hfixed actingElement))
    have htrace := coprimeActionTrace_of_fixed (Actor := OtherActor) (element : Value) hotherFixed
    exact htrace.symm.trans element.property
  have hkernelTrivial : Subsingleton traceKernel := by
    by_contra hnontrivial
    let : Nontrivial traceKernel := not_subsingleton_iff_nontrivial.mp hnontrivial
    let : Nontrivial (Multiplicative traceKernel) :=
      Multiplicative.toAdd.symm.nontrivial
    obtain ⟨exponent, hpositive, hcard⟩ := hkernelPGroup.nontrivial_iff_card.mp inferInstance
    have hcardKernel := Nat.card_congr
      (Multiplicative.toAdd : Multiplicative traceKernel ≃ traceKernel)
    have hdivisibility : prime ∣ Nat.card traceKernel := by
      rw [← hcardKernel, hcard]
      exact dvd_pow_self _ (Nat.ne_of_gt hpositive)
    obtain ⟨element, hfixed, hnonzero⟩ :=
      hactor.exists_fixed_point_of_prime_dvd_card_of_fixed_point traceKernel hdivisibility
        (a := 0) (fun actingElement => smul_zero actingElement)
    let fixedKernel := FixedPoints.addSubgroup Actor traceKernel
    have hfixedKernelPGroup : IsPGroup prime (Multiplicative fixedKernel) := by
      have hexponent := isPGroup_iff_pow_pow_eq_one.mp hkernelPGroup
      apply isPGroup_iff_pow_pow_eq_one.mpr
      intro fixedElement
      obtain ⟨exponent, hpower⟩ := hexponent
        (Multiplicative.ofAdd ((Multiplicative.toAdd fixedElement : fixedKernel) : traceKernel))
      refine ⟨exponent, ?_⟩
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd hpower
    have hfixedKernelNontrivial : Nontrivial fixedKernel := by
      apply not_subsingleton_iff_nontrivial.mp
      intro htrivial
      have hequality := htrivial.elim (⟨element, hfixed⟩ : fixedKernel) 0
      exact hnonzero (congrArg Subtype.val hequality).symm
    let : Nontrivial (Multiplicative fixedKernel) := by infer_instance
    obtain ⟨fixedExponent, hfixedPositive, hfixedCard⟩ :=
      hfixedKernelPGroup.nontrivial_iff_card.mp inferInstance
    have hfixedDivisibility : prime ∣ Nat.card fixedKernel := by
      rw [← Nat.card_congr (Multiplicative.toAdd : Multiplicative fixedKernel ≃ fixedKernel),
        hfixedCard]
      exact dvd_pow_self _ (Nat.ne_of_gt hfixedPositive)
    obtain ⟨primeElement, hprimeOrder⟩ := exists_prime_addOrderOf_dvd_card' prime hfixedDivisibility
    have hprimeKilled : prime • (primeElement : traceKernel) = 0 := by
      have hpower : prime • primeElement = 0 := by
        rw [← hprimeOrder]
        exact addOrderOf_nsmul_eq_zero primeElement
      exact congrArg Subtype.val hpower
    have hprimeZero := hkernelFixedZero (primeElement : traceKernel) hprimeKilled
      primeElement.property
    have hprimeElementZero : primeElement = 0 := Subtype.ext hprimeZero
    rw [hprimeElementZero, addOrderOf_zero] at hprimeOrder
    exact hprime.ne_one hprimeOrder.symm
  have htraceInjective : Function.Injective trace := by
    apply (AddMonoidHom.ker_eq_bot_iff trace).mp
    apply le_bot_iff.mp
    intro element helement
    have hequal := hkernelTrivial.elim (⟨element, helement⟩ : traceKernel) 0
    exact congrArg Subtype.val hequal
  intro otherElement element
  apply htraceInjective
  exact coprimeActionTrace_smul_input otherElement element

theorem abelian_pGroup_trace_fixed_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (htraceCommute : ∀ actingElement : Actor, ∀ element : Value,
      coprimeActionTrace (Actor := OtherActor) (actingElement • element) =
        actingElement • coprimeActionTrace (Actor := OtherActor) element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  exact abelian_pGroup_trace_fixed_order_prime_lemma prime hprime hactor hvalue hcoprime
    htraceCommute (fun element _ => hcentralizes element)

theorem abelian_pGroup_axb_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (hcommute : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element = otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  apply abelian_pGroup_trace_fixed_lemma prime hprime hactor hvalue hcoprime
    (hcentralizes := hcentralizes)
  intro actingElement element
  change (∑ otherElement : OtherActor, otherElement • actingElement • element) =
    actingElement • ∑ otherElement : OtherActor, otherElement • element
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl
    (fun otherElement _ => (hcommute actingElement otherElement element).symm)


theorem abelian_pGroup_normalized_actor_fixed_order_prime_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (normalizingAction : Actor →* MulAut OtherActor)
    (hcompatibility : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, prime • element = 0 →
      (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  apply abelian_pGroup_trace_fixed_order_prime_lemma prime hprime hactor hvalue hcoprime
    (hcentralizes := hcentralizes)
  intro actingElement element
  change (∑ otherElement : OtherActor, otherElement • actingElement • element) =
    actingElement • ∑ otherElement : OtherActor, otherElement • element
  rw [Finset.smul_sum]
  exact (Fintype.sum_equiv (normalizingAction actingElement).toEquiv
    (fun otherElement => actingElement • otherElement • element)
    (fun otherElement => otherElement • actingElement • element)
    (fun otherElement => hcompatibility actingElement otherElement element)).symm

theorem coprime_element_fixed_of_fixed_displacement
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (actingElement : Actor) (element : Value)
    (hfixed : actingElement • (element⁻¹ * actingElement • element) =
      element⁻¹ * actingElement • element) : actingElement • element = element := by
  let displacement := element⁻¹ * actingElement • element
  have hiterate (exponent : ℕ) :
      actingElement ^ exponent • element = element * displacement ^ exponent := by
    induction exponent with
    | zero => simp
    | succ exponent inductionHypothesis =>
      rw [pow_succ', mul_smul, inductionHypothesis, smul_mul', smul_pow',
        hfixed]
      change actingElement • element * displacement ^ exponent =
        element * displacement ^ (exponent + 1)
      rw [pow_succ']
      simp only [displacement, mul_assoc, mul_inv_cancel_left]
  have hactorPower : displacement ^ Nat.card Actor = 1 := by
    have hequality := hiterate (Nat.card Actor)
    rw [pow_card_eq_one', one_smul] at hequality
    exact mul_left_cancel (hequality.symm.trans (mul_one element).symm)
  have hdisplacement : displacement = 1 :=
    (pow_eq_one_iff_of_coprime hcoprime).mp ⟨pow_card_eq_one', hactorPower⟩
  have hequality := congrArg (fun value : Value => element * value) hdisplacement
  simpa only [displacement, mul_inv_cancel_left, mul_one] using hequality

theorem coprime_action_trivial_of_fixed_displacements
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (hfixed : ∀ actingElement : Actor, ∀ element : Value,
      actingElement • (element⁻¹ * actingElement • element) =
        element⁻¹ * actingElement • element) :
    ∀ actingElement : Actor, ∀ element : Value, actingElement • element = element := by
  intro actingElement element
  exact coprime_element_fixed_of_fixed_displacement hcoprime actingElement element
    (hfixed actingElement element)


theorem commutative_pGroup_axb_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Finite OtherActor]
    [CommGroup Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime Value)
    (hcoprime : (Nat.card Value).Coprime (Nat.card OtherActor))
    (hcommute : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element = otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  classical
  let : Fintype OtherActor := Fintype.ofFinite OtherActor
  let actorAction := MulDistribMulAction.toMulAut Actor Value
  let otherAction := MulDistribMulAction.toMulAut OtherActor Value
  let : DistribMulAction Actor (Additive Value) := additiveActionOfMulAutHom actorAction
  let : DistribMulAction OtherActor (Additive Value) := additiveActionOfMulAutHom otherAction
  have hresult := abelian_pGroup_axb_lemma (Value := Additive Value)
    prime hprime hactor hvalue (by
      rw [← Nat.card_congr (Additive.ofMul : Value ≃ Additive Value)]
      simpa only [Nat.card_eq_fintype_card] using hcoprime)
    hcommute hcentralizes
  exact hresult


@[expose] def characteristicQuotientActionHom
    {Actor Value : Type*} [Monoid Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    (hcharacteristic : invariantGroup.Characteristic) :
    Actor →* MulAut (Value ⧸ invariantGroup) where
  toFun actingElement := QuotientGroup.congr invariantGroup invariantGroup
    (action actingElement)
    (by
      rw [← MulEquiv.toMonoidHom_eq_coe]
      exact Subgroup.characteristic_iff_map_eq.mp hcharacteristic (action actingElement))
  map_one' := by
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective invariantGroup element
    simp only [QuotientGroup.congr_mk', map_one, MulAut.one_apply]
  map_mul' := by
    intro first second
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective invariantGroup element
    simp only [MulAut.mul_apply]
    rw [QuotientGroup.congr_mk', QuotientGroup.congr_mk', QuotientGroup.congr_mk', map_mul]
    rfl

theorem pGroup_axb_lemma
    {Actor OtherActor : Type*} {Value : Type u}
    [Group Actor] [Group OtherActor] [Finite OtherActor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime Value)
    (hcoprime : (Nat.card Value).Coprime (Nat.card OtherActor))
    (hcommute : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element = otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  have inductiveClaim : ∀ cardinal : ℕ,
      ∀ (ValueGroup : Type u) [Group ValueGroup] [Finite ValueGroup],
      Nat.card ValueGroup = cardinal →
      ∀ (actorAction : Actor →* MulAut ValueGroup)
        (otherAction : OtherActor →* MulAut ValueGroup),
      IsPGroup prime ValueGroup → (Nat.card ValueGroup).Coprime (Nat.card OtherActor) →
      (∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : ValueGroup,
        actorAction actingElement (otherAction otherElement element) =
          otherAction otherElement (actorAction actingElement element)) →
      (∀ element : ValueGroup,
        (∀ actingElement : Actor, actorAction actingElement element = element) →
        ∀ otherElement : OtherActor, otherAction otherElement element = element) →
      ∀ otherElement : OtherActor, ∀ element : ValueGroup,
        otherAction otherElement element = element := by
    intro cardinal
    induction cardinal using Nat.strong_induction_on with
    | h cardinal inductionHypothesis =>
      intro ValueGroup groupInstance finiteInstance hcardinal actorAction otherAction
        hgroup hgroupCoprime hactionsCommute hfixedCentralized
      let : MulDistribMulAction Actor ValueGroup :=
        multiplicativeActionOfMulAutHom actorAction
      let : MulDistribMulAction OtherActor ValueGroup :=
        multiplicativeActionOfMulAutHom otherAction
      let centralGroup := Subgroup.center ValueGroup
      have hcharacteristic : centralGroup.Characteristic := Subgroup.centerCharacteristic
      let : CommGroup centralGroup := {
        centralGroup.toGroup with
        mul_comm := by
          intro first second
          apply Subtype.ext
          exact Subgroup.mem_center_iff.mp second.property first }
      let centerActorAction := characteristicActionHom actorAction centralGroup hcharacteristic
      let centerOtherAction := characteristicActionHom otherAction centralGroup hcharacteristic
      let : MulDistribMulAction Actor centralGroup :=
        multiplicativeActionOfMulAutHom centerActorAction
      let : MulDistribMulAction OtherActor centralGroup :=
        multiplicativeActionOfMulAutHom centerOtherAction
      have hcenterFixed : ∀ otherElement : OtherActor, ∀ element : centralGroup,
          centerOtherAction otherElement element = element := by
        apply commutative_pGroup_axb_lemma prime hprime hactor
          (hgroup.to_subgroup centralGroup)
          (hgroupCoprime.of_dvd_left centralGroup.card_subgroup_dvd_card)
        · intro actingElement otherElement element
          apply Subtype.ext
          exact hactionsCommute actingElement otherElement element
        · intro element hfixed otherElement
          apply Subtype.ext
          exact hfixedCentralized element
            (fun actingElement => congrArg Subtype.val (hfixed actingElement)) otherElement
      have hcenterFixedAmbient (otherElement : OtherActor) (element : ValueGroup)
          (helement : element ∈ centralGroup) : otherAction otherElement element = element :=
        congrArg Subtype.val (hcenterFixed otherElement ⟨element, helement⟩)
      by_cases hcenterTop : centralGroup = ⊤
      · intro otherElement element
        exact hcenterFixedAmbient otherElement element (hcenterTop ▸ Subgroup.mem_top element)
      · have hnontrivial : Nontrivial ValueGroup := by
          by_contra htrivial
          let : Subsingleton ValueGroup := not_nontrivial_iff_subsingleton.mp htrivial
          apply hcenterTop
          apply top_unique
          intro element _
          exact Subgroup.mem_center_iff.mpr (fun other => Subsingleton.elim _ _)
        let : Nontrivial ValueGroup := hnontrivial
        let : Nontrivial centralGroup := hgroup.center_nontrivial
        have hcenterCard : 1 < Nat.card centralGroup := by
          have hpositive : 0 < Nat.card centralGroup := Nat.card_pos
          have hne : Nat.card centralGroup ≠ 1 := by
            intro hequal
            have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hequal).1
            exact not_subsingleton centralGroup hsubsingleton
          omega
        have hquotientCard : Nat.card (ValueGroup ⧸ centralGroup) < cardinal := by
          have hproduct := centralGroup.index_mul_card
          rw [centralGroup.index_eq_card] at hproduct
          have hpositive : 0 < Nat.card (ValueGroup ⧸ centralGroup) := Nat.card_pos
          have hstrict : Nat.card (ValueGroup ⧸ centralGroup) <
              Nat.card (ValueGroup ⧸ centralGroup) * Nat.card centralGroup := by
            nlinarith
          rwa [hproduct, hcardinal] at hstrict
        let quotientActorAction :=
          characteristicQuotientActionHom actorAction centralGroup hcharacteristic
        let quotientOtherAction :=
          characteristicQuotientActionHom otherAction centralGroup hcharacteristic
        have hquotientApply (groupAction : Actor →* MulAut ValueGroup)
            (actingElement : Actor) (element : ValueGroup) :
            characteristicQuotientActionHom groupAction centralGroup hcharacteristic
                actingElement ((QuotientGroup.mk' centralGroup) element) =
              (QuotientGroup.mk' centralGroup) (groupAction actingElement element) := by
          dsimp only [characteristicQuotientActionHom, MonoidHom.coe_mk, OneHom.coe_mk]
          rw [QuotientGroup.congr_mk']
        have hquotientOtherApply (otherElement : OtherActor) (element : ValueGroup) :
            quotientOtherAction otherElement ((QuotientGroup.mk' centralGroup) element) =
              (QuotientGroup.mk' centralGroup) (otherAction otherElement element) := by
          dsimp only [quotientOtherAction, characteristicQuotientActionHom,
            MonoidHom.coe_mk, OneHom.coe_mk]
          rw [QuotientGroup.congr_mk']
        have hquotientFixed : ∀ otherElement : OtherActor,
            ∀ element : ValueGroup ⧸ centralGroup,
            quotientOtherAction otherElement element = element := by
          apply inductionHypothesis (Nat.card (ValueGroup ⧸ centralGroup)) hquotientCard
            (ValueGroup ⧸ centralGroup) rfl quotientActorAction quotientOtherAction
          · exact hgroup.of_surjective (QuotientGroup.mk' centralGroup)
              (QuotientGroup.mk'_surjective centralGroup)
          · exact hgroupCoprime.of_dvd_left centralGroup.card_quotient_dvd_card
          · intro actingElement otherElement element
            obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective centralGroup element
            rw [hquotientOtherApply, hquotientApply, hquotientApply, hquotientOtherApply]
            exact congrArg (QuotientGroup.mk' centralGroup)
              (hactionsCommute actingElement otherElement preimage)
          · intro element hfixed otherElement
            obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective centralGroup element
            have hdisplacements (actingElement : Actor) :
                preimage⁻¹ * actorAction actingElement preimage ∈ centralGroup := by
              apply QuotientGroup.eq.mp
              exact (hquotientApply actorAction actingElement preimage).symm.trans
                (hfixed actingElement) |>.symm
            have hotherDisplacementFixed : ∀ actingElement : Actor,
                actorAction actingElement (preimage⁻¹ * otherAction otherElement preimage) =
                  preimage⁻¹ * otherAction otherElement preimage := by
              intro actingElement
              let displacement := preimage⁻¹ * actorAction actingElement preimage
              have hdisplacement := hdisplacements actingElement
              have hactorPreimage : actorAction actingElement preimage = preimage * displacement := by
                simp only [displacement, mul_inv_cancel_left]
              have hdisplacementCentral := Subgroup.mem_center_iff.mp hdisplacement
                (preimage⁻¹ * otherAction otherElement preimage)
              change (preimage⁻¹ * otherAction otherElement preimage) * displacement =
                displacement * (preimage⁻¹ * otherAction otherElement preimage)
                at hdisplacementCentral
              rw [map_mul, map_inv, hactionsCommute, hactorPreimage, map_mul,
                hcenterFixedAmbient otherElement displacement hdisplacement, mul_inv_rev]
              simpa only [mul_assoc, inv_mul_cancel_left] using
                congrArg (fun value : ValueGroup => displacement⁻¹ * value)
                  hdisplacementCentral
            have hotherFixedDisplacement :=
              hfixedCentralized (preimage⁻¹ * otherAction otherElement preimage)
                hotherDisplacementFixed otherElement
            have hpreimageFixed := coprime_element_fixed_of_fixed_displacement
              hgroupCoprime otherElement preimage hotherFixedDisplacement
            exact (hquotientOtherApply otherElement preimage).trans
              (congrArg (QuotientGroup.mk' centralGroup) hpreimageFixed)
        apply coprime_action_trivial_of_fixed_displacements hgroupCoprime
        intro otherElement element
        have hdisplacement : element⁻¹ * otherAction otherElement element ∈ centralGroup := by
          apply QuotientGroup.eq.mp
          exact ((hquotientOtherApply otherElement element).symm.trans
            (hquotientFixed otherElement ((QuotientGroup.mk' centralGroup) element))).symm
        exact hcenterFixedAmbient otherElement _ hdisplacement
  exact inductiveClaim (Nat.card Value) Value rfl
    (MulDistribMulAction.toMulAut Actor Value) (MulDistribMulAction.toMulAut OtherActor Value)
    hvalue hcoprime hcommute hcentralizes

theorem ambient_subgroup_axb_centralizer_le
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime)
    (actingGroup otherGroup valueGroup : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hvalue : IsPGroup prime valueGroup)
    (hcoprime : (Nat.card valueGroup).Coprime (Nat.card otherGroup))
    (hactorNormalizes : actingGroup ≤ Subgroup.normalizer (valueGroup : Set G))
    (hotherNormalizes : otherGroup ≤ Subgroup.normalizer (valueGroup : Set G))
    (hcommute : otherGroup ≤ Subgroup.centralizer (actingGroup : Set G))
    (hcentralizes : otherGroup ≤ Subgroup.centralizer
      ((valueGroup ⊓ Subgroup.centralizer (actingGroup : Set G) : Subgroup G) : Set G)) :
    otherGroup ≤ Subgroup.centralizer (valueGroup : Set G) := by
  let actorAction := ambientSubgroupActionHom actingGroup valueGroup hactorNormalizes
  let otherAction := ambientSubgroupActionHom otherGroup valueGroup hotherNormalizes
  let : MulDistribMulAction actingGroup valueGroup :=
    multiplicativeActionOfMulAutHom actorAction
  let : MulDistribMulAction otherGroup valueGroup :=
    multiplicativeActionOfMulAutHom otherAction
  have hactionsCommute : ∀ actingElement : actingGroup, ∀ otherElement : otherGroup,
      ∀ element : valueGroup,
      actingElement • otherElement • element = otherElement • actingElement • element := by
    intro actingElement otherElement element
    apply Subtype.ext
    have hcommuting := Subgroup.mem_centralizer_iff.mp
      (hcommute otherElement.property) actingElement actingElement.property
    have hconj := congrArg (fun automorphism : MulAut G => automorphism (element : G))
      (congrArg MulAut.conj hcommuting)
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at hconj
    change ((actorAction actingElement (otherAction otherElement element)) : G) =
      ((otherAction otherElement (actorAction actingElement element)) : G)
    simpa only [actorAction, otherAction, ambientSubgroupActionHom_apply_coe,
      MulAut.conj_apply] using hconj
  have hfixedCentralized : ∀ element : valueGroup,
      (∀ actingElement : actingGroup, actingElement • element = element) →
      ∀ otherElement : otherGroup, otherElement • element = element := by
    intro element hfixed otherElement
    have helementCentralizes : (element : G) ∈ Subgroup.centralizer (actingGroup : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro actingElement hactingElement
      have hequality := congrArg Subtype.val (hfixed ⟨actingElement, hactingElement⟩)
      change actingElement * (element : G) * actingElement⁻¹ = element at hequality
      have hcancel := congrArg (fun value : G => value * actingElement) hequality
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
    have hcommuting := Subgroup.mem_centralizer_iff.mp
      (hcentralizes otherElement.property) element ⟨element.property, helementCentralizes⟩
    apply Subtype.ext
    change (otherElement : G) * (element : G) * (otherElement : G)⁻¹ = element
    rw [← hcommuting, mul_inv_cancel_right]
  have hresult := pGroup_axb_lemma prime hprime hactor hvalue hcoprime
    hactionsCommute hfixedCentralized
  intro otherElement hotherElement
  apply Subgroup.mem_centralizer_iff.mpr
  intro element helement
  have hequality := congrArg Subtype.val
    (hresult ⟨otherElement, hotherElement⟩ ⟨element, helement⟩)
  change otherElement * element * otherElement⁻¹ = element at hequality
  have hcancel := congrArg (fun value : G => value * otherElement) hequality
  have hequal : otherElement * element = element * otherElement := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
  exact hequal.symm


theorem normalizer_le_normalizer_centralizer
    {G : Type*} [Group G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (subgroup : Set G) : Set G) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (subgroup : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (subgroup : Set G))

theorem common_normalizer_le_normalizer_inf
    {G : Type*} [Group G] (actingGroup firstGroup secondGroup : Subgroup G)
    (hfirst : actingGroup ≤ Subgroup.normalizer (firstGroup : Set G))
    (hsecond : actingGroup ≤ Subgroup.normalizer (secondGroup : Set G)) :
    actingGroup ≤ Subgroup.normalizer ((firstGroup ⊓ secondGroup : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actingElement hactingElement element helement
  exact ⟨(Subgroup.le_normalizer_iff.mp hfirst actingElement hactingElement element helement.1),
    (Subgroup.le_normalizer_iff.mp hsecond actingElement hactingElement element helement.2)⟩


theorem pCore_map_mulEquiv_le
    {Source Target : Type*} [Group Source] [Group Target]
    (prime : ℕ) (equivalence : Source ≃* Target) :
    (pCore prime Source).map equivalence.toMonoidHom ≤ pCore prime Target := by
  exact normal_pGroup_le_pCore prime _
    ((pCore_normal prime).map equivalence.toMonoidHom equivalence.surjective)
    ((pCore_isPGroup prime).map equivalence.toMonoidHom)

theorem pCore_map_mulEquiv
    {Source Target : Type*} [Group Source] [Group Target]
    (prime : ℕ) (equivalence : Source ≃* Target) :
    (pCore prime Source).map equivalence.toMonoidHom = pCore prime Target := by
  apply le_antisymm (pCore_map_mulEquiv_le prime equivalence)
  have hreverse := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (pCore_map_mulEquiv_le prime equivalence.symm)
  have hcomp : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom =
      MonoidHom.id Target := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at hreverse

theorem pCoreOf_map_subtype
    {G : Type*} [Group G] (prime : ℕ) (overgroup : Subgroup G)
    (localGroup : Subgroup overgroup) :
    (pCoreOf prime localGroup).map overgroup.subtype =
      pCoreOf prime (localGroup.map overgroup.subtype) := by
  let equivalence := localGroup.equivMapOfInjective overgroup.subtype
    overgroup.subtype_injective
  have hhom : (localGroup.map overgroup.subtype).subtype.comp equivalence.toMonoidHom =
      overgroup.subtype.comp localGroup.subtype := by
    ext element
    rfl
  unfold pCoreOf
  rw [← pCore_map_mulEquiv prime equivalence, Subgroup.map_map, Subgroup.map_map, hhom]


theorem coprime_quotient_preserves_order_prime_centralizer_condition
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target]
    (prime : ℕ) (hprime : prime.Prime) (actingGroup : Subgroup Source)
    (hactor : IsPGroup prime actingGroup)
    (homomorphism : Source →* Target) (hsurjective : Function.Surjective homomorphism)
    (hcoprime : prime.Coprime (Nat.card homomorphism.ker))
    (hcontains : ∀ element : Source,
      element ∈ Subgroup.centralizer (actingGroup : Set Source) →
      orderOf element = prime → element ∈ actingGroup) :
    ∀ element : Target,
      element ∈ Subgroup.centralizer (actingGroup.map homomorphism : Set Target) →
      orderOf element = prime → element ∈ actingGroup.map homomorphism := by
  let : Fact prime.Prime := ⟨hprime⟩
  let sourceAction := MulAut.conj.comp actingGroup.subtype
  let targetAction := MulAut.conj.comp (homomorphism.comp actingGroup.subtype)
  let : MulDistribMulAction actingGroup Source := multiplicativeActionOfMulAutHom sourceAction
  let : MulDistribMulAction actingGroup Target := multiplicativeActionOfMulAutHom targetAction
  let : MulAction actingGroup Source :=
    (multiplicativeActionOfMulAutHom sourceAction).toMulAction
  let : MulAction actingGroup Target :=
    (multiplicativeActionOfMulAutHom targetAction).toMulAction
  intro element hcentralizes horder
  have hfixed : ∀ actingElement : actingGroup, actingElement • element = element := by
    intro actingElement
    change homomorphism actingElement * element * (homomorphism actingElement)⁻¹ = element
    have hcommute := Subgroup.mem_centralizer_iff.mp hcentralizes (homomorphism actingElement)
      (Subgroup.mem_map_of_mem homomorphism actingElement.property)
    rw [hcommute, mul_inv_cancel_right]
  have hequivariant : ∀ actingElement : actingGroup, ∀ sourceElement : Source,
      homomorphism (actingElement • sourceElement) =
        actingElement • homomorphism sourceElement := by
    intro actingElement sourceElement
    change homomorphism ((actingElement : Source) * sourceElement * (actingElement : Source)⁻¹) =
      homomorphism actingElement * homomorphism sourceElement * (homomorphism actingElement)⁻¹
    rw [map_mul, map_mul, map_inv]
  obtain ⟨preimage, hpreimage, hpreimageFixed⟩ := coprime_pGroup_fixed_lift prime hprime hactor
    homomorphism hsurjective hequivariant hcoprime element hfixed
  let primeElement := preimage ^ Nat.card homomorphism.ker
  have hprimePower : primeElement ^ prime = 1 := by
    have hkernel : preimage ^ prime ∈ homomorphism.ker := by
      rw [MonoidHom.mem_ker, map_pow, hpreimage, ← horder]
      exact pow_orderOf_eq_one element
    have hpower : (⟨preimage ^ prime, hkernel⟩ : homomorphism.ker) ^
        Nat.card homomorphism.ker = 1 := pow_card_eq_one'
    have hambient := congrArg Subtype.val hpower
    simpa only [primeElement, Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul, Nat.mul_comm]
      using hambient
  have hprimeImage : homomorphism primeElement = element ^ Nat.card homomorphism.ker := by
    dsimp only [primeElement]
    rw [map_pow, hpreimage]
  have hprimeNontrivial : primeElement ≠ 1 := by
    intro hequal
    have hpower : element ^ Nat.card homomorphism.ker = 1 := by
      rw [← hprimeImage, hequal, map_one]
    have hpowerPrime : element ^ prime = 1 := by
      rw [← horder]
      exact pow_orderOf_eq_one element
    have helementOne := (pow_eq_one_iff_of_coprime hcoprime).mp ⟨hpowerPrime, hpower⟩
    rw [helementOne, orderOf_one] at horder
    exact hprime.ne_one horder.symm
  have hprimeCentralizes : primeElement ∈ Subgroup.centralizer (actingGroup : Set Source) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro actingElement hactingElement
    have hfixedPreimage := hpreimageFixed (⟨actingElement, hactingElement⟩ : actingGroup)
    have hfixedPower : (⟨actingElement, hactingElement⟩ : actingGroup) • primeElement =
        primeElement := by
      dsimp only [primeElement]
      rw [smul_pow', hfixedPreimage]
    change actingElement * primeElement * actingElement⁻¹ = primeElement at hfixedPower
    have hcancel := congrArg (fun value : Source => value * actingElement) hfixedPower
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
  have hprimeActor := hcontains primeElement hprimeCentralizes
    (orderOf_eq_prime hprimePower hprimeNontrivial)
  have hpowerActor : element ^ Nat.card homomorphism.ker ∈ actingGroup.map homomorphism := by
    rw [← hprimeImage]
    exact Subgroup.mem_map_of_mem homomorphism hprimeActor
  apply (Subgroup.zpowers_le.mpr hpowerActor)
  apply mem_zpowers_pow_iff.mpr
  rw [horder]
  exact hcoprime.symm


end CFSG.RankThreeCoreUniqueness.Helpers
