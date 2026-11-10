module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank
public import CFSG.LocalAnalysis.LargeEvenClassification.LiftSquareMap
public import CFSG.LocalAnalysis.LargeEvenClassification.DeepLiftCommutation
public import CFSG.LocalAnalysis.LargeEvenClassification.LiftSquareInjection
public import CFSG.LocalAnalysis.LargeEvenClassification.PrincipalNorm

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def deepAbelianAutomorphisms (Abelian : Type groupUniverse) [CommGroup Abelian] :
    Subgroup (MulAut Abelian) :=
  (principalFourSubgroup (AddMonoid.End (Additive Abelian))).comap
    (abelianAutomorphismUnits Abelian)

theorem deepAbelianAutomorphisms_normal (Abelian : Type groupUniverse) [CommGroup Abelian] :
    (deepAbelianAutomorphisms Abelian).Normal := by
  let : (principalFourSubgroup (AddMonoid.End (Additive Abelian))).Normal :=
    principal_four_normal _
  exact Subgroup.Normal.comap inferInstance (abelianAutomorphismUnits Abelian)

theorem deepAbelianAutomorphisms_power_difference {Abelian : Type groupUniverse} [CommGroup Abelian]
    (automorphism : MulAut Abelian) (hdeep : automorphism ∈ deepAbelianAutomorphisms Abelian)
    (element : Abelian) : ∃ source : Abelian, automorphism element * element⁻¹ = source ^ 4 := by
  obtain ⟨operator, hoperator⟩ := hdeep
  have haction := congrArg (fun endomorphism : AddMonoid.End (Additive Abelian) =>
    endomorphism (Additive.ofMul element)) hoperator
  change Additive.ofMul (automorphism element) = Additive.ofMul element +
    4 • operator (Additive.ofMul element) at haction
  refine ⟨(operator (Additive.ofMul element)).toMul, ?_⟩
  have heq := congrArg Additive.toMul haction
  change automorphism element = element * (operator (Additive.ofMul element)).toMul ^ 4 at heq
  rw [heq, mul_comm element]
  group

theorem deepAbelianAutomorphisms_involutions {Abelian : Type groupUniverse} [CommGroup Abelian]
    [Finite Abelian] (hpgroup : IsPGroup 2 Abelian) :
    ∃ Involutions : Subgroup (MulAut Abelian), Involutions.Normal ∧ IsElemAbelian 2 Involutions ∧
      ∀ automorphism : MulAut Abelian, automorphism ∈ Involutions ↔
        automorphism ∈ deepAbelianAutomorphisms Abelian ∧ automorphism ^ 2 = 1 := by
  obtain ⟨exponent, hcharacteristic⟩ := pGroup_addEnd_binary_characteristic hpgroup
  let Deep := deepAbelianAutomorphisms Abelian
  let : Deep.Normal := deepAbelianAutomorphisms_normal Abelian
  have hcommute : ∀ first ∈ Deep, ∀ second ∈ Deep,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second := by
    intro first hfirst second hsecond hsquare _
    apply abelianAutomorphismUnits_injective Abelian
    rw [map_mul, map_mul]
    exact principal_involution_central hcharacteristic
      ((abelianAutomorphismUnits Abelian) first) ((abelianAutomorphismUnits Abelian) second)
      hfirst hsecond (by rw [← map_pow, hsquare, map_one])
  let Involutions := normalSquareOneSubgroup Deep hcommute
  exact ⟨Involutions, normalSquareOneSubgroup_normal Deep hcommute,
    normalSquareOneSubgroup_elementary Deep hcommute, fun _ => Iff.rfl⟩

theorem exists_deep_conjugation_square_injection {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnoEight : ∀ Eight : Subgroup Ambient, Eight.Normal → IsElemAbelian 2 Eight → Nat.card Eight ≠ 8)
    (hcard : Nat.card (normalElementarySquareKernel Normal hcommutative) = 4)
    (hroot : ∀ element : Normal,
      (element : Ambient) ^ 2 ∈ normalPowerSubgroup Normal hcommutative 4 →
        (element : Ambient) ∈ normalPowerSubgroup Normal hcommutative 2) :
    let _ : CommGroup Normal := { (inferInstance : Group Normal) with
      mul_comm := @mul_comm' Normal _ hcommutative }
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ∃ Involutions : Subgroup (MulAut Normal), IsElemAbelian 2 Involutions ∧
      (∀ automorphism : MulAut Normal, automorphism ∈ Involutions ↔
        automorphism ∈ deepAbelianAutomorphisms Normal ∧ automorphism ^ 2 = 1 ∧
          automorphism ∈ (MulAut.conjNormal (H := Normal)).range) ∧
      ∃ squareMap : Involutions →* (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2),
        Function.Injective squareMap ∧
        ∀ lift : Ambient, ∀ automorphism : Involutions,
          MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
            squareMap automorphism =
              (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (lift ^ 2) := by
  dsimp only
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let Power := normalPowerSubgroup Normal hcommutative 2
  let : Power.Normal := normalPowerSubgroup_normal Normal hcommutative 2
  let action : Ambient →* MulAut Normal := MulAut.conjNormal
  obtain ⟨Full, hfullNormal, hfullElementary, hfullShape⟩ :=
    deepAbelianAutomorphisms_involutions (hpgroup.to_subgroup Normal)
  let Involutions := Full ⊓ action.range
  have helementary : IsElemAbelian 2 Involutions :=
    elementary_subgroup_of_le Full Involutions hfullElementary inf_le_left
  have hshape : ∀ automorphism : MulAut Normal, automorphism ∈ Involutions ↔
      automorphism ∈ deepAbelianAutomorphisms Normal ∧ automorphism ^ 2 = 1 ∧
        automorphism ∈ action.range := by
    intro automorphism
    change (automorphism ∈ Full ∧ automorphism ∈ action.range) ↔ _
    rw [hfullShape]
    tauto
  have hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      action lift = (automorphism : MulAut Normal) := by
    intro automorphism
    exact automorphism.property.2
  have hstable : ∀ conjugator : Ambient, ∀ automorphism : MulAut Normal,
      automorphism ∈ Involutions → action conjugator * automorphism * (action conjugator)⁻¹ ∈
        Involutions := by
    intro conjugator automorphism helement
    exact ⟨hfullNormal.conj_mem automorphism helement.1 (action conjugator),
      action.range.mul_mem (action.range.mul_mem ⟨conjugator, rfl⟩ helement.2)
        (action.range.inv_mem ⟨conjugator, rfl⟩)⟩
  have hdeepLift : ∀ lift : Ambient, action lift ∈ Involutions → ∀ element : Normal,
      lift * (element : Ambient) * lift⁻¹ * (element : Ambient)⁻¹ ∈
        normalPowerSubgroup Normal hcommutative 4 := by
    intro lift hlift element
    obtain ⟨source, hsource⟩ := deepAbelianAutomorphisms_power_difference (action lift)
      ((hshape _).mp hlift).1 element
    apply (normalPowerSubgroup_mem Normal hcommutative 4 _).mpr
    refine ⟨source, ?_⟩
    have heq := congrArg (fun entry : Normal => (entry : Ambient)) hsource
    change (MulAut.conjNormal (H := Normal) lift element : Ambient) * (element : Ambient)⁻¹ =
      (source : Ambient) ^ 4 at heq
    rw [MulAut.conjNormal_apply] at heq
    exact heq.symm
  have hquotientCommute : ∀ first second : Ambient,
      action first ∈ Involutions → action second ∈ Involutions →
        Commute ((QuotientGroup.mk' Power) first) ((QuotientGroup.mk' Power) second) := by
    intro first second hfirst hsecond
    apply deep_lifts_commute_mod_squares Normal hcommutative hselfCentralizing first second
      ((hshape _).mp hfirst).2.1
    · exact congrArg (fun entry : Involutions => (entry : MulAut Normal))
        (@mul_comm' Involutions _ helementary.1 ⟨_, hfirst⟩ ⟨_, hsecond⟩)
    · exact hdeepLift first hfirst
    · exact hdeepLift second hsecond
    · exact hroot
  obtain ⟨squareMap, hsquares⟩ := exists_conjugation_lift_square Normal hcommutative
    hselfCentralizing Involutions hlifts hquotientCommute
  refine ⟨Involutions, helementary, hshape, squareMap, ?_, hsquares⟩
  apply conjugation_lift_square_injective hpgroup Normal hcommutative hselfCentralizing hnoEight
    hcard Involutions hstable helementary hlifts _ _ squareMap hsquares
  · intro automorphism
    exact (abelian_principal_norm (hpgroup.to_subgroup Normal) automorphism
      ((hshape _).mp automorphism.property).1).1
  · intro automorphism
    exact (abelian_principal_norm (hpgroup.to_subgroup Normal) automorphism
      ((hshape _).mp automorphism.property).1).2


end CFSG.LargeEvenClassification.Helpers
