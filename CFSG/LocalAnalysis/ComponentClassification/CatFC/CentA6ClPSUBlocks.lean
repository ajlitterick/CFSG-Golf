module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUBase
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUCent
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcCommon
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Walter.JRFacts
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.GH74.Generic.Shapes
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.GH74.Statements
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.J4Base
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.ConjSimple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Open.StandardDefs
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import Lean.Data.Json

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

section Blocks

variable {f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 3 f E)
  {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem psu_exists_perfect_unitary_three {B' : W →ₛₗ[h.bar] W →ₗ[E] E} (hsym : B'.IsSymm)
    (hl : B'.SeparatingLeft) (hW : 3 ≤ finrank E W) :
    ∃ (Q : Type) (_ : Group Q) (j : Q →* sesqUnitaryGroup B'), Function.Injective j ∧
      commutator Q = ⊤ ∧ 27 ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := h.finite
  obtain ⟨hsig2, hsig1, -⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data 3 f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply 3 f h.card_eq_sq
  have hfix := OddInner.card_fixedSubfield hsig2 hsig1 h.card_eq_sq
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hsym hl
  have hq3 : 3 ≤ 3 ^ f := OddInner.three_le_pow Nat.prime_three (by norm_num) h.one_le
  have hnq : (finrank E W, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq))) ≠ (3, 2) := by
    rw [hfix]
    intro h32
    have h2 : 3 ^ f = 2 := (Prod.mk.inj h32).2
    omega
  have hq := CatalogueBUnitaryIsometry.specialIsometry_quasisimple_of_three_le B' hsym hnd hsig2
    hsig1 hW hnq
  let Y : Subgroup (CatalogueBUnitaryIsometry.isometryGroup
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq) B') :=
    CatalogueBUnitaryIsometry.specialIsometry
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq) B'
  have hY : CFSG.IsComponent Y := ⟨hq, (MonoidHom.normal_ker _).isSubnormal⟩
  refine ⟨↥Y, inferInstance,
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h B').symm.toMonoidHom.comp Y.subtype,
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h B').symm.injective.comp Y.subtype_injective,
    Group.isPerfect_def.mp hq.1, ?_⟩
  obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu Nat.prime_three (by norm_num) h.one_le
    h.card_eq_sq hW B' hsym hnd hsig2 hsig1 hsig hY (MonoidHom.id Y) Function.surjective_id
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
      rw [hx]
      exact one_mem _)
  have h1 := OddSelector.prime_cube_dvd_card_psu Nat.prime_three h.one_le h.card_eq_sq hW
  rw [← Nat.card_congr eX.toEquiv] at h1
  simpa using h1

theorem psu_exists_perfect_unitary_two (hO : LieOrderFormulasInput) {B' : W →ₛₗ[h.bar] W →ₗ[E] E}
    (hsym : B'.IsSymm) (hl : B'.SeparatingLeft) (hW : finrank E W = 2) (hf : 2 ≤ f) :
    ∃ (Q : Type) (_ : Group Q) (j : Q →* sesqUnitaryGroup B'), Function.Injective j ∧
      commutator Q = ⊤ ∧ (3 ≤ f → 27 ∣ Nat.card (Q ⧸ Subgroup.center Q)) ∧
      (f = 2 → Nat.card (Q ⧸ Subgroup.center Q) = 360) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := h.finite
  obtain ⟨hsig2, hsig1, -⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data 3 f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply 3 f h.card_eq_sq
  have hfix := OddInner.card_fixedSubfield hsig2 hsig1 h.card_eq_sq
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hsym hl
  have h9 : 9 ≤ 3 ^ f := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq)) ≠ 2 := by
    rw [hfix]; omega
  have hq3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq)) ≠ 3 := by
    rw [hfix]; omega
  have hq := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple B' hsym hnd hsig2 hsig1 hW
    hq2 hq3
  obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
    (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq) B' hsym hnd hsig2 hsig1 hW
  have hadm : StatedLieAdmissible .PSL 2 3 f :=
    OddInner.admissible_PSL Nat.prime_three h.one_le le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  have hmod : LieModel (Matrix.SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E
      (CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq)) ⧸ Subgroup.center _)
      .PSL 2 3 f :=
    Or.inl ⟨by decide, LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 _
      hadm hfix⟩
  have hmodQ := LieModel.of_mulEquiv
    (QuotientGroup.congr _ _ eSL.symm (Subgroup.map_center_eq eSL.symm)) hmod
  refine ⟨↥(CatalogueBUnitaryIsometry.specialIsometry
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation 3 f h.card_eq_sq) B'),
    inferInstance,
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h B').symm.toMonoidHom.comp (Subgroup.subtype _),
    (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h B').symm.injective.comp
      (Subgroup.subtype_injective _),
    Group.isPerfect_def.mp hq.1, fun h3 => ?_, fun h2 => ?_⟩
  · exact psu_dvd_27_of_lieModel hO hadm hmodQ (by simp [lieSylowExponent]; omega)
  · subst h2
    exact psu_card_of_lieModel_psl_two_nine hO hadm hmodQ

include h in
theorem psu_dvd_27_card_specialLinear (hO : LieOrderFormulasInput) (m : ℕ) (hm : 2 ≤ m)
    (hcase : 3 ≤ m ∨ 2 ≤ f) :
    27 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) := by
  haveI : Finite E := h.finite
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hk : Nat.card E = 3 ^ (2 * f) := h.card
  have hq3 : 3 ≤ 3 ^ (2 * f) :=
    OddInner.three_le_pow Nat.prime_three (by norm_num) (by have := h.one_le; omega)
  have hadm : StatedLieAdmissible .PSL (m' + 1) 3 (2 * f) :=
    OddInner.admissible_PSL Nat.prime_three (by have := h.one_le; omega) hm
      (Or.inr (by have := h.one_le; have : 9 ≤ 3 ^ (2 * f) := by
                    calc 9 = 3 ^ 2 := by norm_num
                      _ ≤ 3 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
                  omega))
      (Or.inr (by have := h.one_le; have : 9 ≤ 3 ^ (2 * f) := by
                    calc 9 = 3 ^ 2 := by norm_num
                      _ ≤ 3 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
                  omega))
  have hmod : LieModel (Matrix.SpecialLinearGroup (Fin (m' + 1)) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) E)) .PSL (m' + 1) 3 (2 * f) :=
    Or.inl ⟨by decide, LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m' E
      hadm hk⟩
  refine psu_dvd_27_of_lieModel hO hadm hmod ?_
  have hf := h.one_le
  simp only [lieSylowExponent]
  rcases hcase with h3 | h2
  · have : 3 ≤ (m' + 1) * (m' + 1 - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      exact Nat.mul_le_mul h3 (by omega)
    calc 3 ≤ (m' + 1) * (m' + 1 - 1) / 2 := this
      _ ≤ (m' + 1) * (m' + 1 - 1) / 2 * (2 * f) := Nat.le_mul_of_pos_right _ (by omega)
  · have hm2 : m' = 1 ∨ 2 ≤ m' := by omega
    rcases hm2 with rfl | hm2
    · simp
      omega
    · have : 3 ≤ (m' + 1) * (m' + 1 - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        exact Nat.mul_le_mul (by omega) (by omega)
      calc 3 ≤ (m' + 1) * (m' + 1 - 1) / 2 := this
        _ ≤ (m' + 1) * (m' + 1 - 1) / 2 * (2 * f) := Nat.le_mul_of_pos_right _ (by omega)

include h in
theorem psu_exists_perfect_GL (hO : LieOrderFormulasInput) (hW : 2 ≤ finrank E W)
    (hcase : 3 ≤ finrank E W ∨ 2 ≤ f) :
    ∃ (Q : Type) (_ : Group Q) (j : Q →* LinearMap.GeneralLinearGroup E W),
      Function.Injective j ∧ commutator Q = ⊤ ∧ 27 ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  haveI : Finite E := h.finite
  have hk : Nat.card E = 3 ^ (2 * f) := h.card
  have h9 : 9 ≤ 3 ^ (2 * f) := by
    have := h.one_le
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := CatalogueBGeneralLinear.specialLinear_quasisimple (finrank E W) E hW
    (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨Matrix.SpecialLinearGroup (Fin (finrank E W)) E, inferInstance,
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis E W)).toMulEquiv).symm.toMonoidHom.comp
      Matrix.SpecialLinearGroup.toGL,
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis E W)).toMulEquiv).symm.injective.comp
      Matrix.SpecialLinearGroup.toGL_injective,
    Group.isPerfect_def.mp hq.1, psu_dvd_27_card_specialLinear h hO (finrank E W) hW hcase⟩

end Blocks

end CFSG.ComponentClassification.CatFC
