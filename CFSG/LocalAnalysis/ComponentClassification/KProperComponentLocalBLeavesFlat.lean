module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9E
public import CFSG.LocalAnalysis.ComponentClassification.GSFMTripleBranchU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CH
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33Narrow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82TcA10T
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0Fuse
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Close
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURows
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ProdU4
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMNKMH
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SClosedKSMax
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXTw
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDRowM
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDRowP
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Sp4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuActL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuActL2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QD4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QRee
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QPSU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QPSL
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Wire
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQ
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURWire
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaMain
import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Open
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveTB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldFactor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XFacts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Open
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3U4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Spin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LE7Inv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Row
import CFSG.LocalAnalysis.ComponentClassification.GSThmB82TcRed
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226S
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgF
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwMem
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwOrbGS3P
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWCoset
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSw46
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCaseTwoW3
public import CFSG.Holt.H78.Theorem1
public import CFSG.Holt.H78.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeNDiag
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormC3
public import CFSG.LocalAnalysis.OddStandard.ChengHeldFinalHyp
public import CFSG.LocalAnalysis.OddStandard.RouteWStdONan
public import CFSG.LocalAnalysis.OddStandard.ONanB2Mirror
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbAltR
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixH
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFOpenCycOddJ
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSCATTwo
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalStageU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixC

public noncomputable section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint

section Certified

theorem gsInputs_of_flatLeavesGS
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) (h2An : GSThmB.Solomon2AnInput)
    (hSCAT2 : SolAltLit.AltStdCyclicOddTwoFalse) (hSwX : SolMax.SwapP2.SwapMemberResidueNineExact)
    (hSw9T2 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (hSw9T3 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (hFC6' : SolMax.SignalizerNineSixDihedralLocalInput)
    (hGS : GSLit.GriessSolomonInput) (hZA10T : GSThmB.GS82CentXA10TransferInput)
    (h2z : GSThmB.GS82Step2FuseInput) :
    GSLit.ThompsonBurgoyneInput ∧ SolAltLit.SolomonAlternatingOddInput ∧ GSLit.GriessSolomonInput ∧
      GSLit.TheoremBBoundedInput ∧ GSLit.HarrisInput :=
  have hPSU4 : HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .PSU 4 1 :=
    HarrisLit.T1.P58b3.harris82Lemma58bThreeRowAt_PSU_four
  have hR2 : HarrisLit.T1.Harris82Lemma413Three := HarrisLit.T1.harris82Lemma413Three_holds
  have h226S : HarrisLit.T1.Harris82Lemma226ThreeSolvable :=
    HarrisLit.T1.harris82Lemma226ThreeSolvable_holds
  have caseA10ε0 : GSThmB.GS82CaseA10EpsZeroInput :=
    GSThmB.gs82CaseA10EpsZeroInput_of_transfer hZA10T
  have h6U0 : GSThmB.GS82Step6PumpInputA0 :=
    GSThmB.gs82Step6PumpInputA0_of_classical RankThree.PartOne.SPOR.schreierFor_catalog
      CatFactsL4U4.cfL4U4Prod GSThmB.cfQPUJ6Classical_holds
  have h6T0 : GSThmB.GS82Step6ThreeInputA0 :=
    GSThmB.gs82Step6ThreeInputA0_holds RankThree.PartOne.SPOR.schreierFor_catalog hCI
      FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
  have hCaseA : GSThmB.GS82CaseAL4U4Input :=
    GSThmB.gs82CaseAL4U4Input_of_fuse RankThree.PartOne.SPOR.schreierFor_catalog hCI
      FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds CatFactsL4U4.cfL4U4Prod
      h2z h6U0 h6T0
  have hR1 : HarrisLit.T1.Spin8CentreFixedOutAbelian := HarrisLit.T1.spin8CentreFixedOutAbelian
  have hE7K : HarrisLit.T1.P58b3L.E7ThreeNoKlein := HarrisLit.T1.P58b3L.e7ThreeNoKlein_holds
  have hPlus4 : HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus 4 1 :=
    HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaPlus_four
  have hDI : SolMax.SignalizerDiagInvertedInput := SolMax.signalizerDiagInvertedInput_holds
  have hMinus4 : HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaMinus 4 1 :=
    HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaMinus_of_four_le
      TBLit.griessMultipliersAllModels_holds le_rfl
  have hPlusE : ∀ n : ℕ, Even n → 4 ≤ n →
      HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 :=
    fun n _ hn => by
      rcases Nat.lt_or_ge n 5 with h | h
      · obtain rfl : n = 4 := by omega
        exact hPlus4
      · exact HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaPlus_of_five_le h
  have hFTE6 : HarrisLit.T1.P51Q.FamF .twistedE6 := HarrisLit.T1.P51Q.famF_twistedE6
  have hOrth : HarrisLit.T1.F3FG.Harris82OutQuatThreeOrth :=
    HarrisLit.T1.F3FG.harris82OutQuatThreeOrth_holds
  have hPSL4 : HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .PSL 4 1 :=
    HarrisLit.T1.P58b3.harris82Lemma58bThreeRowAt_PSL_four
  have hFHe : SolMax.SignalizerFivePumpHeldInput := SolMax.signalizerFivePumpHeldInput_holds
  have hFE7 : HarrisLit.T1.P51Q.FamF .E7 := HarrisLit.T1.P51Q.famF_E7
  have hD4 : HarrisLit.T1.F3FG.FourGroupResidualStepD4 :=
    HarrisLit.T1.F3FG.fourGroupResidualStepD4_of_inputs hR1 hR2
      HarrisLit.T1.harris82ThetaBalanceThree_holds
  have hPSp2 : HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .PSp 2 1 :=
    HarrisLit.T1.P58b3.harris82Lemma58bThreeRowAt_PSp_two
  have hPlus : ∀ n : ℕ, 4 ≤ n → HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 :=
    fun n hn => by
      rcases Nat.even_or_odd n with he | ho
      · exact hPlusE n he hn
      · exact HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaPlus_one
          TBLit.griessMultipliersAllModels_holds (by obtain ⟨k, rfl⟩ := ho; omega) ho
  have hMinus : ∀ n : ℕ, 4 ≤ n → HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaMinus n 1 :=
    fun n hn => by
      rcases Nat.lt_or_ge n 5 with h | h
      · obtain rfl : n = 4 := by omega
        exact hMinus4
      · exact HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaMinus_one
          TBLit.griessMultipliersAllModels_holds h
  have hE7 : HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .E7 0 1 :=
    HarrisLit.T1.harris82Lemma58bThreeRowAt_E7_of_noKlein hE7K
  have hS := RankThree.PartOne.SPOR.schreierFor_catalog
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := GrSLit.gls3OddLieAutComponentsInput_holds
  have h13 : Sol76T13.SolomonThm13Simple := Sol76T13.solomonThm13Simple_of_schreier hS hb
  have hPump : Sol78.AlternatingPumpUpInput :=
    SolMax.alternatingPumpUpInput_of_gls3 hGLS SolMax.suzOuterComponentsInput_holds
      (SolMax.onOuterComponentsInput_of_local SolMax.ONOut.onOuterLocalInput_holds)
  have hSch : SolAltLit.SchurAlternatingMultiplierInput :=
    Alternating.Multipliers.schurAlternatingMultiplierInput
  have hSig : GSThmB.SolomonSignalizerInput :=
    Sol78.solomonSignalizer_of_inputs h2An hCI hS hSch
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate hPump
  have hN1 : SolMax.TwoGroupAltCoverExclusion :=
    SolMax.twoGroupAltCoverExclusion_of_inputs hSig hSch hPump
  have hMLI : Sol78.MaximalityLemmaInput := SolMax.maximalityLemmaInput_of_signalizer hPump hSig
  have hHeP : SolMax.SignalizerHeldPumpExclusionInput :=
    SolMax.signalizerHeldPumpExclusionInput_holds hPump hN1 h13 hMLI hSch
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
  have hFL2 : SolMax.SignalizerFivePumpLTwoInput :=
    SolMax.signalizerFivePumpLTwoInput_holds hPump hN1 h13 hMLI hSch
  have hF3i : SolMax.SignalizerFivePumpBetaInvInput :=
    SolMax.signalizerFivePumpBetaInvInput_of_diagInverted Sol78.balanceTwoComponentInput_holds
      hPump h13 hMLI hSch hDI
  have hF3d : SolMax.SignalizerFivePumpBetaDiagInput :=
    SolMax.signalizerFivePumpBetaDiagInput_of_betaInv Sol78.balanceTwoComponentInput_holds hPump
      h13 hMLI hSch hF3i
  have hF3b : SolMax.SignalizerFivePumpBetaSevenInput :=
    SolMax.signalizerFivePumpBetaSevenInput_of_betaDiag hPump hF3d
  have hF3m : SolMax.SignalizerFivePumpThreeFixMemInput :=
    SolMax.signalizerFivePumpThreeFixMemInput_of_four
      (SolMax.signalizerFivePumpThreeFixFourInput_of_betaSeven Sol78.balanceTwoComponentInput_holds
        hPump hN1 h13 hMLI hSch hF3b)
  have hF3 : SolMax.SignalizerFivePumpThreeFixInput :=
    SolMax.signalizerFivePumpThreeFixInput_of_mem hPump hN1 h13 hMLI hSch hF3m
  have hFL34 : SolMax.SignalizerFivePumpLThreeFourInput :=
    SolMax.signalizerFivePumpLThreeFourInput_of_cert Sol78.balanceTwoComponentInput_holds
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have h51 : HarrisLit.T1.Harris82Lemma51Quat :=
    HarrisLit.T1.P51Q.harris82Lemma51Quat_of_famF HarrisLit.T1.P51Q.famF_psl
      HarrisLit.T1.P51Q.famF_psu HarrisLit.T1.P51Q.famF_PSp HarrisLit.T1.P51Q.famF_POmegaOdd
      HarrisLit.T1.P51Q.famF_POmegaPlus HarrisLit.T1.P51Q.famF_POmegaMinus HarrisLit.T1.P51Q.famF_G2
      HarrisLit.T1.P51Q.famF_F4 HarrisLit.T1.P51Q.famF_E6 hFE7 HarrisLit.T1.P51Q.famF_E8 hFTE6
      HarrisLit.T1.P51Q.famF_trialityD4 HarrisLit.T1.P51Q.famF_twistedG2
  have h51E4 : HarrisLit.T1.Harris82Lemma51E4 :=
    HarrisLit.T1.P51Q.harris82Lemma51E4_of_famF HarrisLit.T1.P51Q.famF_psl
      HarrisLit.T1.P51Q.famF_psu HarrisLit.T1.P51Q.famF_PSp HarrisLit.T1.P51Q.famF_POmegaOdd
      HarrisLit.T1.P51Q.famF_POmegaPlus HarrisLit.T1.P51Q.famF_POmegaMinus HarrisLit.T1.P51Q.famF_G2
      HarrisLit.T1.P51Q.famF_F4 HarrisLit.T1.P51Q.famF_E6 hFE7 HarrisLit.T1.P51Q.famF_E8 hFTE6
      HarrisLit.T1.P51Q.famF_trialityD4 HarrisLit.T1.P51Q.famF_twistedG2
  have hPSU : ∀ n : ℕ, Even n → 6 ≤ n → HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .PSU n 1 :=
    fun n _ h6 => by
      intro G _ _ z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z hm
      exact HarrisLit.T1.harris82Lemma58bThreeRow_PSU_of_six_le h51E4 h6 G z₁ z₂ hz₁ hz₂ hne hc L₁
        L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z 1 hm
  have hOut : HarrisLit.T1.Harris82OutQuatThree :=
    HarrisLit.T1.F3FG.harris82OutQuatThree_of_orth hOrth
  have h58 : HarrisLit.T1.Harris82Lemma58bThree :=
    HarrisLit.T1.harris82Lemma58bThree_of_rowsAt h51E4 hPSL4 hPSU4 hPSp2
      hPSU
      hPlus hMinus hE7
  have h4 : HarrisLit.T1.Harris82FourGroupThree :=
    HarrisLit.T1.F3FG.harris82FourGroupThree_of_inputs hCI
      (HarrisLit.T1.F3FG.knownRowThree_holds hCI h51)
      (HarrisLit.T1.harris82Lemma226Three_of_solvable h226S)
      (HarrisLit.T1.F3FG.fourGroupResidualStep_of_outQuat hOut hD4
        HarrisLit.T1.harris82ThetaBalanceThree_holds)
  have hL34FUM : TBLit.L34FieldUnitaryMaximalStep :=
    TBLit.l34FieldUnitaryMaximalStep_of_griessSolomon hGS
  have hSig : GSThmB.SolomonSignalizerInput :=
    Sol78.solomonSignalizer_of_inputs h2An hCI hS
      Alternating.Multipliers.schurAlternatingMultiplierInput
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate hPump
  have hTB : SolMax.SignalizerFivePumpTBInput :=
    SolMax.signalizerFivePumpTBInput_of_inputs Sol78.balanceTwoComponentInput_holds
      FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds hS hCI
      (Burgoyne.burgoynePropA_of_E1_E2 CatLeafProof.burgoyneExcOddCoreInput_holds
        (Burgoyne.E2.burgoynePropAE6E7_of_twisted
          ⟨Burgoyne.E2.burgoyneE2TwistedE7Input_holds,
            Burgoyne.E2.burgoyneE2TwistedE6Input_of_nonF4
              (Burgoyne.E2.burgoyneE2TwistedE6NonF4Input_of_nonGraph
                (Burgoyne.E2.TwE6In.burgoyneE2TwistedE6NonGraphInput_of_t1
                  Burgoyne.E2.burgoyneE2TwistedE6T1Input_holds))⟩))
      (Burgoyne.burgoynePropB_of_inputs hGA
        (Burgoyne.burgoynePropBE7S_of_fieldQuat CatLeafProof.burgoyneE7FieldQuat_holds)
        Burgoyne.burgoynePropBClassicalS_holds
        Burgoyne.DX.Kl.burgoynePropBSpinPlusKleinInput_holds
        (Burgoyne.DX.Dr.burgoynePropBDrExcInput_of_klein
          Burgoyne.DX.Kl.burgoynePropBSpinPlusKleinInput_holds)
        Burgoyne.DX.burgoynePropBPlusFourInput_holds)
      Burgoyne.burgoynePropC_holds
      (TBLit.l34PumpUpExclusion_of_fieldUnitary
        (TBLit.l34FieldUnitaryExclusion_of_maximal h13 hL34FUM))
      hSig Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate hGA
      RankThree.PartTwo.Sec4.Census.griessMultipliersCentralCovers
  have hFE5 : SolMax.SignalizerFivePumpExactInput :=
    SolMax.signalizerFivePumpExactInput_of_cases Sol78.balanceTwoComponentInput_holds hTB hF3 hFL2
      hFHe hFL34
  have h9s : SolMax.SignalizerSmallDegreeNineInput :=
    SolMax.signalizerSmallDegreeNineInput_of_fivePump Sol78.balanceTwoComponentInput_holds hPump hN1
      (SolMax.signalizerFivePumpBalanceInput_of_exact Sol78.balanceTwoComponentInput_holds hFE5)
  have hsmall : SolMax.SignalizerSmallDegreeInput :=
    SolMax.signalizerSmallDegreeInput_of_nine Sol78.balanceTwoComponentInput_holds hPump hN1 hHeP
      h9s
  have h33 : Sol78.BalanceLemmaInput :=
    SolMax.balanceLemmaInput_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1 hsmall
  have h2 : SolMax.SignalizerCaseTwoFinishInput :=
    SolMax.signalizerCaseTwoFinishInput_of_w h33 h13 hMLI hSch
      (SolMax.signalizerCaseTwoWInput_holds h13 hMLI hSch)
  have hFC8 : SolMax.SignalizerNineFusionCountEightInput :=
    SolMax.signalizerNineFusionCountEightInput_holds Sol78.balanceTwoComponentInput_holds h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      h13 hMLI hSch hPump hN1
  have hFCs : SolMax.SignalizerNineFusionCountSplitInput :=
    SolMax.signalizerNineFusionCountSplitInput_of_six_local Sol78.balanceTwoComponentInput_holds
      h33 (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump
        hN1 hsmall)
      h13 hMLI hSch hPump hN1 hFC8 hFC6'
  have hFCr : SolMax.SignalizerNineFusionCountReducedInput :=
    SolMax.signalizerNineFusionCountReducedInput_of_split h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      h13 hMLI hSch hFCs
  have hFC : SolMax.SignalizerNineFusionCountInput :=
    SolMax.signalizerNineFusionCountInput_of_reduced h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      h13 hMLI hSch hFCr
  have hNFAr : SolMax.SignalizerCaseOneConjugateOutsideAltRInput :=
    SolMax.signalizerCaseOneConjugateOutsideAltRInput_holds h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      h13 hMLI hSch hPump hN1
  have hNFA8 : SolMax.SignalizerCaseOneConjugateOutsideAltEightInput :=
    SolMax.signalizerCaseOneConjugateOutsideAltEightInput_of_altR h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      h13 hMLI hSch hPump hN1 hNFAr
  have hNFA : SolMax.SignalizerCaseOneConjugateOutsideAltInput :=
    SolMax.signalizerCaseOneConjugateOutsideAltInput_of_eight h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      h13 hMLI hSch hPump hN1 hNFA8
  have hCycJ : SolAltLit.AltStdCyclicOddJ := SolAltLit.altStdCyclicOddJ_of_scatTwo hSCAT2
  have hSwN9 : SolMax.SwapP2.SwapMemberResidueNine :=
    SolMax.SwapP2.swapMemberResidueNine_of_leaves h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      hSwX
      (SolMax.SwapP2.swapMemberResidueNineOfClaimA_of_exotic
        (SolMax.SwapP2.swapMemberResidueNineExotic_of_split hSw9T2 hSw9T3))
  have hSwR : SolMax.SwapP2.SwapMemberResidue :=
    SolMax.SwapP2.swapMemberResidue_of_nine h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      hPump hN1 hSwN9
  have hSwN : SolMax.SignalizerSwapMemberNarrowInput :=
    SolMax.SwapP2.signalizerSwapMemberNarrowInput_of_residue h33
      (SolMax.signalizerLemma35_of_smallDegree Sol78.balanceTwoComponentInput_holds hPump hN1
        hsmall)
      hPump hN1 hSwR
  have hSA : SolAltLit.SolomonAlternatingOddInput :=
    SolMax.solomonAlternatingOddInput_of_open_five_cases_alt_cycOddJ
      (RankTwoAlt.rankTwoAlternatingStandard_of_open
          (RankTwoAltFive.altFiveCaseI_of
              (RankTwoAlt.altGenerationFive_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA))
          (RankTwoAltFive.asc310EpsOne_of Asc76X.goldschmidtTheoremA) RankTwoAltFive.asc310IIb
          RankTwoAlt.altFiveM12NotTop_of RankTwoAlt.altEvenCenterSmall RankTwoAlt.altThreeCover
          (RankTwoAlt.altGenerationSmall_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA)
          RankTwoAlt.altRootFusion
          (RankTwoAlt.altTypeTwoFusion_of_rootFusion RankTwoAlt.altRootFusion)
          (RankTwoAlt.altTypeTwoCentralizer Asc76X.goldschmidtTheoremA)) hCI hCycJ h13 hPump hSig hSwN hTB hF3 hFL2
      hFHe hFL34 hHeP h2 hNFA hFC
  have h3 : HarrisLit.T1.Harris82Theorem1FieldThree :=
    HarrisLit.T1.harris82Theorem1FieldThree_of_open h4 h58
  have hES : HarrisLit.Harris81Lemma35IdentEvenSporFact :=
    HarrisLit.harris81Lemma35IdentEvenSporFact_of_spor hGLS hGA
      SolMax.H35.harris81Lemma35IdentSporFact_holds
  have hId35 : HarrisLit.Harris81Lemma35IdentFact :=
    HarrisLit.harris81Lemma35IdentFact_of_nonAlt hCI
      (HarrisLit.harris81Lemma35IdentNonAltFact_of_resid
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
        EvenSporadicStandard.centralTwoBound
        (HarrisLit.harris81Lemma35IdentResidFact_of_cover hGLS hGA
          (HarrisLit.harris81Lemma35IdentCoverFact_of_four
            (HarrisLit.harris81Lemma35IdentFourCoverFact_of_evenSpor hGA hES))))
  have hKMH := gsInputs_of_leavesGS hGH hCI hb h2An hSA hGS
    (GSThmB.A10E1.gs82CaseA10Input_of_epsZero AutL2Facts.cfL2Sylow AutL2Facts.cfL2C
      AutL2Facts.cfL2J AutL2Facts.cfL2Rank CatFactsSp4.cfSec8JOrder caseA10ε0)
    hCaseA
    (HarrisLit.T1.harris82Theorem1KProper_of_open hCI hId35
      h3 (HarrisLit.T1.S74.solomon74SpinSevenAsUsed_of HarrisLit.T1.S74.lemma38_holds
          HarrisLit.T1.S74.f1_holds HarrisLit.T1.S74.f2b_holds
          (HarrisLit.T1.S74.spinFactsAll_of HarrisLit.T1.S74.f1_holds HarrisLit.T1.S74.f2b_holds
              HarrisLit.T1.S74.f4_holds HarrisLit.T1.S74.a1_holds HarrisLit.T1.S74.a2_holds
              HarrisLit.T1.S74.a3_holds HarrisLit.T1.S74.a4_holds)))
  ⟨hKMH.1, hSA, hGS, hKMH.2.1, hKMH.2.2⟩
theorem tripleBranch_of_flatLeavesGS
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) (h2An : GSThmB.Solomon2AnInput)
    (hSCAT2 : SolAltLit.AltStdCyclicOddTwoFalse) (hSwX : SolMax.SwapP2.SwapMemberResidueNineExact)
    (hSw9T2 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (hSw9T3 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (hFC6' : SolMax.SignalizerNineSixDihedralLocalInput)
    (hGS : GSLit.GriessSolomonInput) (hFMU : FooteLit.FooteMaximalUnbalancedInput)
    (hZA10T : GSThmB.GS82CentXA10TransferInput) (h2z : GSThmB.GS82Step2FuseInput) :
    UFrontier.TripleBranch := by
  obtain ⟨hTB, hSA, -, hB, hH⟩ :=
    gsInputs_of_flatLeavesGS hGH hCI hb h2An hSCAT2 hSwX hSw9T2 hSw9T3 hFC6' hGS hZA10T h2z
  exact GSFM.tripleBranch_of_inputsU hTB hSA hGS hB hH GSLit.globallyFirstRankTwoInput_holds hFMU
    (HSFLit.hsflitA7_of_inputs hGH OddStandard.Harada75.haradaInput_holds
      HSFLit.Sec8.fritz812dNotSylow)
    hCI

structure FlatBundleGS : Prop where
  h2An : GSThmB.Solomon2AnInput
  hSCAT2 : SolAltLit.AltStdCyclicOddTwoFalse
  hSwX : SolMax.SwapP2.SwapMemberResidueNineExact
  hSw9T2 : SolMax.SwapP2.SwapMemberResidueNineExoticT2
  hSw9T3 : SolMax.SwapP2.SwapMemberResidueNineExoticT3
  hFC6' : SolMax.SignalizerNineSixDihedralLocalInput
  hGS : GSLit.GriessSolomonInput
  hFMU : FooteLit.FooteMaximalUnbalancedInput
  hZA10T : GSThmB.GS82CentXA10TransferInput
  h2z : GSThmB.GS82Step2FuseInput

theorem tripleBranch_of_flatBundleGS
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) (hL : FlatBundleGS) :
    UFrontier.TripleBranch :=
  tripleBranch_of_flatLeavesGS hGH hCI hb hL.h2An hL.hSCAT2 hL.hSwX hL.hSw9T2 hL.hSw9T3
    hL.hFC6' hL.hGS hL.hFMU hL.hZA10T hL.h2z

theorem kProper_component_local_B_of_flatLeavesGS
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) (h2An : GSThmB.Solomon2AnInput)
    (hSCAT2 : SolAltLit.AltStdCyclicOddTwoFalse) (hSwX : SolMax.SwapP2.SwapMemberResidueNineExact)
    (hSw9T2 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (hSw9T3 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (hFC6' : SolMax.SignalizerNineSixDihedralLocalInput)
    (hGS : GSLit.GriessSolomonInput) (hFMU : FooteLit.FooteMaximalUnbalancedInput)
    (hZA10T : GSThmB.GS82CentXA10TransferInput) (h2z : GSThmB.GS82Step2FuseInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hK : KProper Catalog G)
    (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_frontier hGH
    (tripleBranch_of_flatLeavesGS hGH hCI hb h2An hSCAT2 hSwX hSw9T2 hSw9T3 hFC6' hGS hFMU
      hZA10T h2z)
    G hK hcomp

end Certified

end CFSG.ComponentClassification.KProperRelativeB
