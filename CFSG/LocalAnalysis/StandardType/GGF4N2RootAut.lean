module


public import CFSG.GH74.Generic.S1.RAutLin



public import CFSG.LocalAnalysis.StandardType.GGF4N2RootCharts
public import CFSG.LocalAnalysis.StandardType.GGPComponentInvolutionNormalizer
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSL
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLLevi
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLCent
public import CFSG.Fischer.Aut.Complete
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAut
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinus
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusConj
public import CFSG.HardMathSupport.Foote.Proving.OrderSL4
public import CFSG.Models.PGLOrders


public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSLAux

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist

public import CFSG.Quasithin.EmptyFaithful.ModGRed1

public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeAHelp
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEightLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinA
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.ModGSolv
public import CFSG.Sporadic.McL

public section

namespace CFSG.StandardType

open Matrix CFSG.RankThree.PartOne.K159
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]


private abbrev PSL4 (F : Type) [Field F] := projectiveSL 4 F


end CFSG.StandardType

namespace CFSG.StandardType
open Matrix CFSG.RankThree.PartOne.K159
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
variable {F : Type} [Field F] [CharP F 2] [Finite F]

private abbrev PSL6 (F : Type) [Field F] := projectiveSL 6 F


end CFSG.StandardType

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.SpecialLinear

variable {F : Type} [Field F] [CharP F 2] [Finite F]


end CFSG.StandardType

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]


end CFSG.StandardType

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]


end CFSG.StandardType

namespace CFSG.StandardType

section MinusNativeRoot

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra


end MinusNativeRoot

section ActualRootCharts

open CFSG.Open CFSG.Assembly
open CFSG.ClassicalGroups.SpecialLinear CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal.Spin.Twisted (minusFrame)


end ActualRootCharts

section MarkedRootInjection
open CFSG.Assembly


end MarkedRootInjection

section BadLineQuotientCharts

open Matrix CFSG.Assembly CFSG.ClassicalGroups.SpecialLinear


end BadLineQuotientCharts


end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.StandardType
open Matrix


end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.SeitzReduction.E6Pilot
open Matrix

variable {F : Type} [Field F]


end CFSG.StandardType

namespace CFSG.StandardType

open Matrix

variable {F : Type} [Field F] [Finite F]


end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Glauberman Matrix


end CFSG.StandardType

namespace CFSG.StandardType
open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction


open CFSG.RankThree.CALinearPlane
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBGraphForm


open CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm


end CFSG.StandardType


public section

namespace CFSG.StandardType.N2KFieldCoefficient

open Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

noncomputable section

abbrev F4 : Type := GaloisField 2 2
abbrev GL6F4 : Type := Matrix.GeneralLinearGroup (Fin 6) F4
abbrev SL6F4 : Type := Matrix.SpecialLinearGroup (Fin 6) F4

abbrev root01 : (0 : Fin 6) ≠ 1 := by decide
abbrev root10 : (1 : Fin 6) ≠ 0 := by decide

abbrev rootTransvection (t : F4) : SL6F4 :=
  SpecialLinearGroup.transvection root01 t

abbrev slConjugation6 (A : GL6F4) : MulAut SL6F4 :=
  slConjugation 6 F4 A

abbrev slFieldAut6 (σ : F4 ≃+* F4) : MulAut SL6F4 :=
  slFieldAut (Fin 6) F4 σ

abbrev slGraphAut6 : MulAut SL6F4 :=
  slGraphAut 6 F4

@[expose] noncomputable def fieldDetectionBeta (A : GL6F4) (σ : F4 ≃+* F4) (ε : ℕ) :
    MulAut SL6F4 :=
  slConjugation6 A * slFieldAut6 σ * (slGraphAut6) ^ ε

noncomputable def rootDirection (ε : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  if ε = 0 then Matrix.single (0 : Fin 6) 1 1 else Matrix.single (1 : Fin 6) 0 1

private lemma fieldAut_transvection (σ : F4 ≃+* F4) {i j : Fin 6} (hij : i ≠ j) (t : F4) :
    ((slFieldAut6 σ (SpecialLinearGroup.transvection hij t) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      1 + σ t • Matrix.single i j 1 := by
  change ((slFieldEquiv (Fin 6) σ
    (SpecialLinearGroup.transvection hij t) : SL6F4) : Matrix (Fin 6) (Fin 6) F4) = _
  ext a b
  rw [slFieldEquiv_entry]
  rw [SpecialLinearGroup.transvection_coe]
  by_cases h : a = i ∧ b = j
  · rcases h with ⟨rfl, rfl⟩
    simp [Matrix.smul_apply, Matrix.single, Matrix.one_apply]
  · have h' : ¬ (i = a ∧ j = b) := by
      intro hh
      exact h ⟨hh.1.symm, hh.2.symm⟩
    simp [Matrix.smul_apply, Matrix.single, Matrix.one_apply, h, h']

private lemma graphAut_transvection (t : F4) :
    ((slGraphAut6 (rootTransvection t) : SL6F4) : Matrix (Fin 6) (Fin 6) F4) =
      1 + t • Matrix.single (1 : Fin 6) 0 1 := by
  rw [slGraphAut_matrix]
  have hinv : (rootTransvection t)⁻¹ =
      SpecialLinearGroup.transvection root01 (-t) :=
    SpecialLinearGroup.transvection_inv root01 t
  rw [hinv]
  rw [show (-t : F4) = t by rw [CharTwo.neg_eq]]
  rw [SpecialLinearGroup.transvection_coe]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  ext a b
  simp [Matrix.smul_apply, Matrix.single, Matrix.one_apply]

set_option maxHeartbeats 1000000 in
private lemma conjugation_transvection (A : GL6F4) {i j : Fin 6} (hij : i ≠ j) (t : F4) :
    ((slConjugation6 A (SpecialLinearGroup.transvection hij t) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      1 + t • ((A : Matrix (Fin 6) (Fin 6) F4) * Matrix.single i j 1 *
        ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
  rw [slConjugation_matrix]
  rw [SpecialLinearGroup.transvection_coe]
  let E : Matrix (Fin 6) (Fin 6) F4 := Matrix.single i j 1
  have hAA : ((A : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL6F4) :
      Matrix (Fin 6) (Fin 6) F4)) = 1 := Units.mul_inv A
  rw [show Matrix.single i j t = t • E by
    change Matrix.single i j t = t • Matrix.single i j 1
    rw [Matrix.smul_single]
    simp]
  calc
    ((A : Matrix (Fin 6) (Fin 6) F4) * (1 + t • E) *
        ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) =
        (((A : Matrix (Fin 6) (Fin 6) F4) * 1 +
          (A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.mul_add]
    _ = (((A : Matrix (Fin 6) (Fin 6) F4) +
          (A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.mul_one]
    _ = ((A : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL6F4) :
          Matrix (Fin 6) (Fin 6) F4)) +
          (((A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.add_mul]
    _ = 1 + (((A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
          ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [hAA]
    _ = 1 + ((t • ((A : Matrix (Fin 6) (Fin 6) F4) * E)) *
          ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Algebra.mul_smul_comm]
    _ = 1 + (t • (((A : Matrix (Fin 6) (Fin 6) F4) * E) *
          ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4))) := by
      rw [Algebra.smul_mul_assoc]
    _ = 1 + t • ((A : Matrix (Fin 6) (Fin 6) F4) *
          Matrix.single i j 1 *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.mul_assoc]


private lemma fieldAut_transvection_eq (σ : F4 ≃+* F4) {i j : Fin 6} (hij : i ≠ j) (t : F4) :
    slFieldAut6 σ (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (σ t) := by
  apply Subtype.ext
  rw [fieldAut_transvection, SpecialLinearGroup.transvection_coe]
  rw [Matrix.smul_single]
  simp

private lemma graphAut_transvection_eq (t : F4) :
    slGraphAut6 (rootTransvection t) =
      SpecialLinearGroup.transvection root10 t := by
  apply Subtype.ext
  rw [graphAut_transvection, SpecialLinearGroup.transvection_coe]
  rw [Matrix.smul_single]
  simp

private lemma beta_root_matrix (A : GL6F4) (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1)
    (t : F4) :
    ((fieldDetectionBeta A σ ε (rootTransvection t) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      1 + σ t • ((A : Matrix (Fin 6) (Fin 6) F4) * rootDirection ε *
        ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
  interval_cases ε
  · have hbeta : fieldDetectionBeta A σ 0 = slConjugation6 A * slFieldAut6 σ := by
      simp [fieldDetectionBeta]
    rw [hbeta, MulAut.mul_apply]
    rw [fieldAut_transvection_eq σ root01 t]
    rw [conjugation_transvection A root01 (σ t)]
    simp [rootDirection]
  · have hbeta : fieldDetectionBeta A σ 1 =
        slConjugation6 A * slFieldAut6 σ * slGraphAut6 := by
      simp [fieldDetectionBeta]
    rw [hbeta, MulAut.mul_apply, MulAut.mul_apply]
    rw [graphAut_transvection_eq t]
    rw [fieldAut_transvection_eq σ root10 t]
    rw [conjugation_transvection A root10 (σ t)]
    simp [rootDirection]


theorem sigma_eq_refl_of_root_linear
    (A : GL6F4) (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1)
    (hlin : ∀ t : F4,
      ((fieldDetectionBeta A σ ε (rootTransvection t) : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) =
        1 + t • (((fieldDetectionBeta A σ ε (rootTransvection 1) : SL6F4) :
          Matrix (Fin 6) (Fin 6) F4) - 1)) :
    σ = RingEquiv.refl F4 := by
  let D : Matrix (Fin 6) (Fin 6) F4 :=
    (A : Matrix (Fin 6) (Fin 6) F4) * rootDirection ε *
      ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)
  have hformula : ∀ t : F4,
      ((fieldDetectionBeta A σ ε (rootTransvection t) : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) = 1 + σ t • D := by
    intro t
    simpa [D] using beta_root_matrix A σ hε t
  have hbeta1 : ((fieldDetectionBeta A σ ε (rootTransvection 1) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) = 1 + D := by
    simpa using hformula 1
  have htv1 : rootTransvection 1 ≠ (1 : SL6F4) := by
    intro h
    have hentry := congrArg (fun g : SL6F4 => ((g : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) 0 1) h
    have hleft : ((rootTransvection 1 : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) 0 1 = 1 := by
      simp [rootTransvection, SpecialLinearGroup.transvection_coe]
    have hright : (((1 : SL6F4) : Matrix (Fin 6) (Fin 6) F4) 0 1) = 0 := by
      simp
    rw [hleft, hright] at hentry
    exact one_ne_zero hentry
  have hbeta1ne : fieldDetectionBeta A σ ε (rootTransvection 1) ≠ 1 := by
    intro h
    have h' : fieldDetectionBeta A σ ε (rootTransvection 1) =
        fieldDetectionBeta A σ ε 1 := by
      simpa using h
    exact htv1 ((fieldDetectionBeta A σ ε).injective h')
  have hDne : D ≠ 0 := by
    intro hD
    apply hbeta1ne
    apply Subtype.ext
    rw [hbeta1, hD, add_zero]
    rfl
  have hD_eq : ∀ t : F4, σ t • D = t • D := by
    intro t
    have h := hlin t
    rw [hformula t] at h
    have hsub : ((1 + D : Matrix (Fin 6) (Fin 6) F4) - 1) = D := by
      abel
    rw [hbeta1, hsub] at h
    exact add_left_cancel h
  have hD_entry : ∃ i j : Fin 6, D i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hDne
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hD_entry
  have hσt : ∀ t : F4, σ t = t := by
    intro t
    have h := congrFun (congrFun (hD_eq t) i) j
    have h' : σ t * D i j = t * D i j := by
      simpa [Matrix.smul_apply] using h
    exact mul_right_cancel₀ hij h'
  apply RingEquiv.ext
  intro t
  exact hσt t


end

end CFSG.StandardType.N2KFieldCoefficient


public section

namespace CFSG.StandardType.N2KActualAutomorphism

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable section

variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev SL6F (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 6) F
abbrev PSL6F (F : Type) [Field F] : Type := projectiveSL 6 F

private theorem ker_eq_bot_or_center
    (hF : Nat.card F = 4) {Q : Type} [Group Q]
    (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (SL6F F)) :
    ψ.ker = ⊥ ∨ ψ.ker = Subgroup.center (SL6F F) := by
  classical
  have hcardC : Nat.card (Subgroup.center (SL6F F)) = 3 := by
    dsimp [SL6F]
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
    norm_num
  have hcard_dvd : Nat.card ψ.ker ∣ 3 := by
    rw [← hcardC]
    exact Subgroup.card_dvd_of_le hker
  have hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hcard_dvd
  rcases hcard with h1 | h3
  · left
    exact Subgroup.eq_bot_of_card_le ψ.ker (by omega)
  · right
    apply Subgroup.eq_of_le_of_card_ge hker
    rw [hcardC, h3]

private theorem exists_quotient_equiv_projective
    {Q : Type} [Group Q] (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center (SL6F F)) :
    ∃ e : Q ≃* PSL6F F, ∀ g : SL6F F, e (ψ g) = proj 6 F g := by
  classical
  let S := SL6F F
  let P := PSL6F F
  let π : S →* P := proj 6 F
  have hkerπ : ψ.ker = π.ker := by
    dsimp [π, S, P]
    rw [ker_proj, scalars_eq_center]
    exact hker
  let eψ : S ⧸ ψ.ker ≃* Q :=
    QuotientGroup.liftEquiv (N := ψ.ker) hψ rfl
  let eπ : S ⧸ π.ker ≃* P :=
    QuotientGroup.liftEquiv (N := π.ker) (proj_surjective 6 F) rfl
  let c : S ⧸ ψ.ker ≃* S ⧸ π.ker :=
    QuotientGroup.quotientMulEquivOfEq hkerπ
  refine ⟨eψ.symm.trans (c.trans eπ), ?_⟩
  intro g
  have hψg : eψ.symm (ψ g) = QuotientGroup.mk g := by
    rw [← QuotientGroup.liftEquiv_mk (N := ψ.ker) hψ rfl g]
    exact eψ.symm_apply_apply _
  have hc : c (QuotientGroup.mk g) = QuotientGroup.mk g :=
    QuotientGroup.quotientMulEquivOfEq_mk hkerπ g
  have hπg : eπ (QuotientGroup.mk g) = π g :=
    QuotientGroup.liftEquiv_mk (N := π.ker) (proj_surjective 6 F) rfl g
  simp only [MulEquiv.trans_apply]
  rw [hψg, hc, hπg]


private theorem exists_std_lift_of_ker_bot
    {Q : Type} [Group Q] (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = ⊥) (αQ : MulAut Q) :
    ∃ (A : GL (Fin 6) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SL6F F,
        αQ (ψ g) = ψ
          (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε) g) := by
  classical
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  let e : SL6F F ≃* Q := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
  let β : MulAut (SL6F F) := MulAut.congr e.symm αQ
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl
      (n := 6) (K := F) (by norm_num) β
  let std : MulAut (SL6F F) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε
  refine ⟨A, σ, ε, hε, ?_⟩
  change ∀ g : SL6F F, αQ (ψ g) = ψ (std g)
  intro g
  have hβg : β g = e.symm (αQ (e g)) := by
    simp [β, MulAut.congr_apply]
  have hcongr : e (β g) = αQ (e g) := by
    rw [hβg]
    exact e.apply_symm_apply (αQ (e g))
  calc
    αQ (ψ g) = e (β g) := by
      rw [hcongr]
      rfl
    _ = e (std g) := by rw [hβ]
    _ = ψ (std g) := rfl


private theorem exists_std_lift_of_ker_center
    {Q : Type} [Group Q] (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center (SL6F F)) (αQ : MulAut Q) :
    ∃ (A : GL (Fin 6) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SL6F F,
        αQ (ψ g) = ψ
          (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε) g) := by
  classical
  obtain ⟨e, he⟩ := exists_quotient_equiv_projective ψ hψ hker
  let αP : MulAut (PSL6F F) := MulAut.congr e αQ
  obtain ⟨A, σ, ε, hε, hgen⟩ :=
    (automorphism_generation (K := F) (n := 6) (by norm_num)).2 αP
  let std : MulAut (SL6F F) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε
  have hdesc : descendAut 6 F std =
      conjAut 6 F A * fieldAut 6 F σ * dualAut 6 F ^ ε := by
    dsimp [std]
    rw [map_mul, map_mul, map_pow]
    rfl
  refine ⟨A, σ, ε, hε, ?_⟩
  change ∀ g : SL6F F, αQ (ψ g) = ψ (std g)
  intro g
  apply e.injective
  have hαP : αP (e (ψ g)) = e (αQ (ψ g)) := by
    simp [αP, MulAut.congr_apply]
  calc
    e (αQ (ψ g)) = αP (e (ψ g)) := hαP.symm
    _ = αP (proj 6 F g) := by rw [he g]
    _ = (conjAut 6 F A * fieldAut 6 F σ * dualAut 6 F ^ ε) (proj 6 F g) := by
      rw [hgen]
    _ = descendAut 6 F std (proj 6 F g) := by rw [hdesc]
    _ = proj 6 F (std g) := descendAut_proj 6 F std g
    _ = e (ψ (std g)) := by rw [he (std g)]


theorem exists_std_lift_of_central_kernel
    (hF : Nat.card F = 4) {Q : Type} [Group Q]
    (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (SL6F F)) (αQ : MulAut Q) :
    ∃ (A : GL (Fin 6) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SL6F F,
        αQ (ψ g) = ψ
          (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε) g) := by
  rcases ker_eq_bot_or_center hF ψ hψ hker with hbot | hcenter
  · exact exists_std_lift_of_ker_bot ψ hψ hbot αQ
  · exact exists_std_lift_of_ker_center ψ hψ hcenter αQ

end

end CFSG.StandardType.N2KActualAutomorphism


public section

namespace CFSG.StandardType.N2KFieldCoefficient
open Matrix CFSG.SeitzReduction.E6Pilot
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.SeitzReduction.LinearPilot

noncomputable section

abbrev GL4F4 : Type := Matrix.GeneralLinearGroup (Fin 4) F4
abbrev SL4F4 : Type := Matrix.SpecialLinearGroup (Fin 4) F4

abbrev root01_4 : (0 : Fin 4) ≠ 1 := by decide

@[expose] noncomputable def blockGamma (C : GL4F4) (δ : ℕ) : MulAut SL4F4 :=
  slConjugation 4 F4 C * (slGraphAut 4 F4) ^ δ

private theorem blockFourMat_affine (t : F4) (M : Matrix (Fin 4) (Fin 4) F4) :
    blockFourMat (1 + t • M) = 1 + t • (blockFourMat (1 + M) - 1) := by
  ext i j
  obtain ⟨i', rfl⟩ := e46.surjective i
  obtain ⟨j', rfl⟩ := e46.surjective j
  rw [blockFourMat_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
  rw [blockFourMat_apply]
  rcases i' with i' | i' <;> rcases j' with j' | j' <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

theorem sigma_eq_refl_of_block_eq
    {Q : Type} [Group Q]
    (psi : SL6F4 →* Q)
    (hpsi_surj : Function.Surjective psi)
    (hpsi_ker : psi.ker ≤ Subgroup.center SL6F4)
    (A : GL6F4)
    (sigma : F4 ≃+* F4)
    (epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (C : GL4F4)
    (delta : ℕ) (hdelta : delta ≤ 1)
    (h : ∀ g : SL4F4,
      psi ((fieldDetectionBeta A sigma epsilon) (blockFour g)) =
        psi (blockFour ((blockGamma C delta) g))) :
    sigma = RingEquiv.refl F4 := by
  haveI hperf : Group.IsPerfect SL4F4 :=
    CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hcomp : ∀ g : SL4F4,
      psi ((fieldDetectionBeta A sigma epsilon).toMonoidHom.comp blockFour g) =
        psi (blockFour.comp (blockGamma C delta).toMonoidHom g) := by
    intro g
    simpa using h g
  have hlift : (fieldDetectionBeta A sigma epsilon).toMonoidHom.comp blockFour =
      blockFour.comp (blockGamma C delta).toMonoidHom :=
    eq_of_comp_eq_of_ker_le_center hpsi_ker hcomp
  have hlin : ∀ t : F4,
      ((fieldDetectionBeta A sigma epsilon (rootTransvection t) : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) =
        1 + t • (((fieldDetectionBeta A sigma epsilon (rootTransvection 1) : SL6F4) :
          Matrix (Fin 6) (Fin 6) F4) - 1) := by
    intro t
    have h1 := congrArg (fun f => f (SpecialLinearGroup.transvection root01_4 t)) hlift
    have hleft_at : ∀ s : F4,
        ((fieldDetectionBeta A sigma epsilon).toMonoidHom.comp blockFour)
          (SpecialLinearGroup.transvection root01_4 s) =
          fieldDetectionBeta A sigma epsilon (rootTransvection s) := by
      intro s
      simp only [MonoidHom.comp_apply, rootTransvection]
      rw [blockFour_transvection]
      have ht : SpecialLinearGroup.transvection (c4_ne root01_4) s =
          SpecialLinearGroup.transvection root01 s := by
        apply Subtype.ext
        simp only [SpecialLinearGroup.transvection_coe]
        rfl
      rw [ht]
      rfl
    have hleft := hleft_at t
    rw [hleft] at h1
    simp only [MonoidHom.comp_apply] at h1
    interval_cases delta
    ·
      have hgamma_at : ∀ s : F4,
          (blockGamma C 0) (SpecialLinearGroup.transvection root01_4 s) =
          slConjugation 4 F4 C (SpecialLinearGroup.transvection root01_4 s) := by
        intro s
        simp [blockGamma]
      have hgamma := hgamma_at t
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection t) =
        blockFour ((blockGamma C 0) (SpecialLinearGroup.transvection root01_4 t)) at h1
      rw [hgamma] at h1
      have hM_all : ∀ s : F4,
          ((slConjugation 4 F4 C (SpecialLinearGroup.transvection root01_4 s) : SL4F4) :
            Matrix (Fin 4) (Fin 4) F4) =
            1 + s • ((C : Matrix (Fin 4) (Fin 4) F4) * Matrix.single (0 : Fin 4) 1 1 *
              ((C⁻¹ : GL4F4) : Matrix (Fin 4) (Fin 4) F4)) := by
        intro s
        rw [slConjugation_matrix]
        rw [SpecialLinearGroup.transvection_coe]
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
        rw [show single (0 : Fin 4) 1 s =
          s • (single (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) F4) by
            rw [Matrix.smul_single, smul_eq_mul, mul_one]]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hM := hM_all t
      have hM1 := hM_all 1
      have h1mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1
      rw [coe_blockFour] at h1mat
      rw [hM] at h1mat
      rw [blockFourMat_affine t] at h1mat
      have h1one := congrArg (fun f => f (SpecialLinearGroup.transvection root01_4 1)) hlift
      rw [hleft_at 1] at h1one
      simp only [MonoidHom.comp_apply] at h1one
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection 1) =
        blockFour ((blockGamma C 0) (SpecialLinearGroup.transvection root01_4 1)) at h1one
      rw [hgamma_at 1] at h1one
      have h1one_mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1one
      rw [coe_blockFour] at h1one_mat
      rw [hM1] at h1one_mat
      simp only [one_smul] at h1one_mat
      rw [← h1one_mat] at h1mat
      exact h1mat
    ·
      have hgamma_at : ∀ s : F4,
          (blockGamma C 1) (SpecialLinearGroup.transvection root01_4 s) =
          slConjugation 4 F4 C (slGraphAut 4 F4 (SpecialLinearGroup.transvection root01_4 s)) := by
        intro s
        simp [blockGamma]
      have hgamma := hgamma_at t
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection t) =
        blockFour ((blockGamma C 1) (SpecialLinearGroup.transvection root01_4 t)) at h1
      rw [hgamma] at h1
      have hM_all : ∀ s : F4,
          ((slConjugation 4 F4 C (slGraphAut 4 F4 (SpecialLinearGroup.transvection root01_4 s)) :
            SL4F4) : Matrix (Fin 4) (Fin 4) F4) =
            1 + s • ((C : Matrix (Fin 4) (Fin 4) F4) * Matrix.single (1 : Fin 4) 0 1 *
              ((C⁻¹ : GL4F4) : Matrix (Fin 4) (Fin 4) F4)) := by
        intro s
        rw [slConjugation_matrix]
        rw [slGraphAut_matrix]
        have hinv : (SpecialLinearGroup.transvection root01_4 s)⁻¹ =
            SpecialLinearGroup.transvection root01_4 (-s) :=
          SpecialLinearGroup.transvection_inv root01_4 s
        rw [hinv]
        rw [show (-s : F4) = s by rw [CharTwo.neg_eq]]
        rw [SpecialLinearGroup.transvection_coe]
        rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
        rw [show single (1 : Fin 4) 0 s =
          s • (single (1 : Fin 4) 0 1 : Matrix (Fin 4) (Fin 4) F4) by
            rw [Matrix.smul_single, smul_eq_mul, mul_one]]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hM := hM_all t
      have hM1 := hM_all 1
      have h1mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1
      rw [coe_blockFour] at h1mat
      rw [hM] at h1mat
      rw [blockFourMat_affine t] at h1mat
      have h1one := congrArg (fun f => f (SpecialLinearGroup.transvection root01_4 1)) hlift
      rw [hleft_at 1] at h1one
      simp only [MonoidHom.comp_apply] at h1one
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection 1) =
        blockFour ((blockGamma C 1) (SpecialLinearGroup.transvection root01_4 1)) at h1one
      rw [hgamma_at 1] at h1one
      have h1one_mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1one
      rw [coe_blockFour] at h1one_mat
      rw [hM1] at h1one_mat
      simp only [one_smul] at h1one_mat
      rw [← h1one_mat] at h1mat
      exact h1mat
  exact sigma_eq_refl_of_root_linear A sigma hepsilon hlin


end

end CFSG.StandardType.N2KFieldCoefficient


public section

namespace CFSG.StandardType

noncomputable section


end

end CFSG.StandardType
