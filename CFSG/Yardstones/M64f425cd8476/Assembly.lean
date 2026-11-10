module

public import CFSG.Yardstones.M64f425cd8476.Definitions
public import CFSG.Quasithin.H13.Assembly
public import CFSG.Quasithin.Vol2.Ch12Sec2Thm12111
public import CFSG.Quasithin.Vol2.Ch8Assembly
public import CFSG.Quasithin.Vol2.Ch3T326H2ShapeHolds
public import CFSG.Quasithin.Background.E6ThreeOpenHeX
public import CFSG.Quasithin.Background.E6TwentyThreePG
public import CFSG.Quasithin.Background.Asc81cPfMain
public import CFSG.Quasithin.Vol2.Ch7Prop711
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Holds
public import CFSG.Quasithin.H13.A6S13820Aut6
public import CFSG.Quasithin.H13.A6S13820AutL2b
public import CFSG.Quasithin.H13.A6S13820AutL3c
public import CFSG.Quasithin.Background.Harris.AutBorel.U3
public import CFSG.Quasithin.Background.Harris.AutBorel.Sp4
public import CFSG.Quasithin.H13.A6S13820AutG2b
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11
public import CFSG.Quasithin.Vol2.Ch12Sec2Wired
public import CFSG.Quasithin.H13.E22CHolds
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11BorelC
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11ARed
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7UW
public import CFSG.Quasithin.H13.A6S13828k
public import CFSG.Quasithin.H13.A6S1356S6Hubs
public import CFSG.Quasithin.H13.F112SliceA5C1Slices
public import CFSG.Quasithin.H13.F112SliceA5C2Slices
public import CFSG.Quasithin.H13.A6S13827iWA5
public import CFSG.Quasithin.H13.GoldschmidtC137ZfDoneW
public import CFSG.Quasithin.Vol2.Ch10Reselect.Wire1317A
public import CFSG.Quasithin.H13.NQS134EY
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.OddStandard.Seitz77U
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.Quasithin.H13.A6S1372L74h
public import CFSG.Quasithin.H13.F112DSPartsC
public import CFSG.Quasithin.Vol2.Ch5Sec1DSC
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4AI
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4EIn
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4R
public import CFSG.RankThree.PartOne.D4RC.RxIso
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
public import CFSG.RankThree.PartTwo.Sec5.Hyp
public import CFSG.RankThree.S4Free.Statement

public section

namespace CFSG.Yardstones.M64f425cd8476

theorem maximal_local_catalog_of_yardstones
    (h01 : Chapter3Theorems) (h02 : Chapter4Theorems) (h03 : CFSG.Quasithin.H13.Stmt5_2_3)
    (h04 : CFSG.Quasithin.H13.Stmt6_2_20) (h05 : Theorem701Steps) (h06 : Section82Steps)
    (h07 : CFSG.Quasithin.H13.Stmt11_0_1) (h08 : Chapter12Section2Inputs)
    (h09 : FiveQuotientEliminations) (h10 : CFSG.Quasithin.H13.InputAS91)
    (h11 : AppendixCFInputs) (h12 : LiteratureRecognitionInputs) (h13 : Chapter13LocalInputs)
    (h14 : Section138Inputs) (h15 : Chapter14Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G),
      CFSG.Quasithin.H13.QTH13 G T L → CFSG.Open.quasithinIsMaximalLocal T L →
        CFSG.Blueprint.Catalog G := by
  have h132 : CFSG.Quasithin.ASInputs.AS_C_1_32 := h11.c132
  have hCorrBig := CFSG.Quasithin.H13.SlotLeaves.burnsideC134w_corrBig_holds
  have hL32M : CFSG.Quasithin.C134L32CorrM := CFSG.Quasithin.MS93.c134L32CorrM_holds
  have h27 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC27Statement G :=
    CFSG.Quasithin.asc27Statement_of_c132 h132
  have h48 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G :=
    CFSG.Quasithin.H13.SlotLeaves.asc48Statement_forall_of_big h132 hCorrBig h12.j4TwoLocals
  have h331 : CFSG.Quasithin.H13.Stmt3_3_1 := h01.stmt3_3_1
  have h3228 := CFSG.Quasithin.Vol2.Ch10.tmpL6_3_2_2_eight_proved
  have h3222 := CFSG.Quasithin.Vol2.Ch10.tmpL6_3_2_2_two_of h3228
    CFSG.Quasithin.H13.stmt3_2_3_proved
  have h3224 := CFSG.Quasithin.Vol2.Ch11.tmpL6_3_2_2_four_of h3222
  have h3226 := CFSG.Quasithin.Vol2.Ch11.tmpL6_3_2_2_six_of CFSG.Quasithin.theoremC58_proved
    CFSG.Quasithin.as317Sylow_proved h331 h3228 h3224
  have h325 : CFSG.Quasithin.H13.Stmt3_2_5 :=
    CFSG.Quasithin.H13.stmt3_2_5_of_c0 CFSG.Quasithin.Ch3T316W.theorem316Statement_holds
      CFSG.Quasithin.H13.d310C0_holds h331 h3222 h3228 h3224 h3226 CFSG.Quasithin.asB56_holds
  have h326 := CFSG.Quasithin.H13.T326.stmt3_2_6C_of_stmt331 h331
  have h711 : CFSG.Quasithin.H13.Stmt7_1_1 :=
    CFSG.Quasithin.H13.Prop711.stmt7_1_1_of h325 (CFSG.Quasithin.H13.stmt3_2_6Lt_of_C h326)
      (CFSG.Quasithin.H13.stmt3_2_9C_of h325 CFSG.Quasithin.Ch3T316W.theorem316Statement_holds)
      h331 CFSG.Quasithin.theoremC58_proved CFSG.Quasithin.as317Sylow_proved
      CFSG.Quasithin.a37ForSQTK_proved CFSG.Quasithin.a38ForSQTK_proved
      CFSG.Quasithin.a39ForSQTK_proved CFSG.Quasithin.H13.stmt3_2_2_eight_proved
  have h701 : CFSG.Quasithin.H13.Stmt7_0_1 :=
    CFSG.Quasithin.H13.stmt7_0_1_of_chain
      (CFSG.Quasithin.H13.stmtFSUModule_of_eight CFSG.Quasithin.H13.stmt3_2_2_eight_proved)
      CFSG.Quasithin.H13.stmt7_0_1_shapeC_holds h711 h05.stmt7_3_5 h05.stmt7_5_2
      h05.stmt7_5_4 h05.stmt7_5_5 h05.stmt7_6_1 h05.stmt8_1_3_M24
      (CFSG.Quasithin.H13.stmt8_2_13_cocode_of h06.stmt8_2_13)
      (CFSG.Quasithin.H13.stmt8_2_14_of h06.stmt8_2_10 h06.stmt8_2_12 h06.stmt8_2_13
        h06.stmt8_2_14_fusion h10)
      h05.stmt8_3_1 (CFSG.Quasithin.H13.stmt9_omegaPlus_of_A h05.stmt9_omegaPlusA)
  have h701A := CFSG.Quasithin.H13.stmt7_0_1A_of_C h701 h326 h05.stmt9_omegaPlusA
  have hE63 : CFSG.Quasithin.ASInputs.AS_E_6_3 :=
    CFSG.Quasithin.E6.as_E_6_3_of_thm104_insp CFSG.Quasithin.Asc81c.Pf.thm104
      CFSG.Quasithin.E6.e623A6Insp_holds
  have hIn10 : CFSG.Quasithin.Vol2.Ch10.Inputs10_0_1A :=
    ⟨h701A, h331, h02.stmt4_2_13, h02.stmt4_4_3, hE63⟩
  have h1001 : CFSG.Quasithin.H13.Stmt10_0_1 :=
    CFSG.Quasithin.Vol2.Ch10.stmt10_0_1_of_remainingA hIn10
  have h1222 : CFSG.Quasithin.H13.Stmt12_2_2 :=
    CFSG.Quasithin.H13.stmt12_2_2_of_12111 h1001 h325 h04 h701 h07 h08.stmt12_1_11
  have h1312 : CFSG.Quasithin.H13.Stmt13_1_2_three :=
    CFSG.Quasithin.H13.stmt13_1_2_three_of_inputs h1222 h09.a7 h09.linear
  have h137 : CFSG.Quasithin.H13.Stmt13_1_7 :=
    CFSG.Quasithin.H13.NQBlock.stmt13_1_7_of_frontierA h1312 hIn10 h701
  have h512 := CFSG.Quasithin.H13.stmt5_1_2_of_asB51 h331 CFSG.Quasithin.B5.asB51_holds
  have hE22 := CFSG.Quasithin.e22StatementNoN_proved
  have h5171 := CFSG.Quasithin.H13.stmt5_1_7_one_of h512 h02.stmt4_3_2
    (CFSG.Quasithin.H13.stmt5_1_7_one_nat_of_two CFSG.Quasithin.B610T.b610Two_holds
      CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds)
    (CFSG.Quasithin.H13.stmt5_1_7_one_A5_of
      (CFSG.Quasithin.E2.e23FourStatement_of hE22 (CFSG.Quasithin.C124.e23Statement_of_e22 hE22))
      h02.stmt4_3_2 CFSG.Quasithin.H13.VolI.stmtC113c
      CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds)
  have h513 := CFSG.Quasithin.H13.stmt5_1_3_of h331 CFSG.Quasithin.theoremC58_proved
    CFSG.Quasithin.Ch3T316W.theorem316Statement_holds CFSG.Quasithin.as317Sylow_proved h512
    (CFSG.Quasithin.H13.stmt5_1_3_qhat_of_asB51
      (CFSG.Quasithin.H13.d310L2Fact_of_d35 CFSG.Quasithin.H13.d35_proved)
      CFSG.Quasithin.Vol2.Ch10.SecA.facts10_1_holds CFSG.Quasithin.asB45_holds
      CFSG.Quasithin.ASInputs.lemI1_6_holds CFSG.Quasithin.B5.asB51_holds
      CFSG.Quasithin.asB42_holds)
  have h516 := CFSG.Quasithin.H13.stmt5_1_6_of_facts h331
    CFSG.Quasithin.theoremC58_proved CFSG.Quasithin.Ch3T316W.theorem316Statement_holds
    CFSG.Quasithin.as317Sylow_proved CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds h512 h513
    CFSG.Quasithin.H13.fact516Quot CFSG.Quasithin.H13.fact516Two CFSG.Quasithin.H13.fact516Orth
  have h5172 : CFSG.Quasithin.H13.Stmt5_1_7_two :=
    CFSG.Quasithin.H13.stmt5_1_7_two_of h331
      CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds CFSG.Quasithin.theoremC58_proved
      CFSG.Quasithin.as317Sylow_proved h5171 h516
  have h3214 := CFSG.Quasithin.H13.NQBlock.stmt3_2_14_of_frontier
    (CFSG.Quasithin.Vol2.Ch10.stmtFSUChoice_of_a36 CFSG.Quasithin.H13.stmt3_2_3_proved
      CFSG.Quasithin.H13.VolI.a36ForSQTK_holds)
    h701 CFSG.Quasithin.Vol2.Ch10.a312ListFactsCat_holds
    CFSG.Quasithin.Ch3T316W.theorem316Statement_holds
  have h1227 : CFSG.Quasithin.H13.Stmt12_2_7 :=
    CFSG.Quasithin.H13.stmt12_2_7_of_unique h331 h1222 h04
      CFSG.Quasithin.a37ForSQTK_proved h3214
  have h12211 : CFSG.Quasithin.H13.Stmt12_2_11' :=
    CFSG.Quasithin.H13.stmt12_2_11_of h331 h1222 CFSG.Quasithin.H13.stmt3_2_3_proved
      (CFSG.Quasithin.H13.stmt12_2_10_of_1222 h1222) CFSG.Quasithin.H13.e22StatementC_holds
      (CFSG.Quasithin.H13.stmt4_4_3_of_orbit' h02.stmt4_4_3)
      (CFSG.Quasithin.H13.lem12211Borel_of_e22 CFSG.Quasithin.H13.e22StatementC_holds)
      (CFSG.Quasithin.H13.lem12211A315_of h1222)
  have h13316 : CFSG.Quasithin.H13.Stmt13_3_16 :=
    CFSG.Quasithin.H13.NQS134.stmt13_3_16_of_remaining h13.stmt13_3_2 h12211 h1227
      (CFSG.Quasithin.H13.U3.u3NondegLineCentralizer_of_comp h13.stmt13_3_2
        CFSG.Quasithin.H13.Frontier331.theorem311
        (CFSG.Quasithin.H13.U3.u3LineComponentExclusion_of_c27W h13.stmt13_3_2 h27 hL32M
          hCorrBig))
      h13.stmt13_3_14
  have h1361 : CFSG.Quasithin.H13.Stmt13_6_1 :=
    CFSG.Quasithin.H13.A5.stmt13_6_1_of_open_noC134_slices h13.stmt13_3_2 h1222 h5172 h331
      h02.stmt4_3_2 h03 h11.sliceA5 h132
  have h13315 : CFSG.Quasithin.H13.A6.Stmt13_3_15 :=
    CFSG.Quasithin.H13.U3.stmt13_3_15_of h13.stmt13_3_2 h13.stmt13_3_14
      (CFSG.Quasithin.H13.A6.u3HatL2Plus_of h13.stmt13_3_2)
  have h1352 : CFSG.Quasithin.H13.A6.Stmt13_5_2 :=
    CFSG.Quasithin.H13.A6.stmt13_5_2_of_inputs h13.stmt13_3_2 h13316 h13.stmt13_4_1
  have h13828 : CFSG.Quasithin.H13.A6.Input13828Six :=
    CFSG.Quasithin.H13.A6.input13828Six_holds h13315
      (CFSG.Quasithin.H13.A6.input1356Two_of h1222
        (CFSG.Quasithin.H13.A6.input1356TwoS6_of_hubs h1222 h13315))
      h13.stmt13_3_14
  have hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK :=
    CFSG.Quasithin.H13.U3.GC137.c137StatementFiveSQTK_of
      (CFSG.Quasithin.H13.U3.c137StatementFive_of_Z
        (CFSG.Quasithin.H13.U3.GC137.c137StatementFiveZ_completeW
          CFSG.Quasithin.e22StatementNoN_proved h132 hL32M))
  have h1339 := CFSG.Quasithin.H13.U3.stmt13_3_9_of h13.stmt13_3_2
    (CFSG.Quasithin.H13.stmt12_2_6_of h1222 CFSG.Quasithin.H13.stmt3_2_3_proved)
    (CFSG.Quasithin.H13.stmt12_2_8_of_inputs h1222
      (CFSG.Quasithin.a318Facts_of_two CFSG.Quasithin.qSporOutTwo_holds
        CFSG.Quasithin.R3c18.qLiePRank_holds)
      CFSG.Quasithin.H13.VolI.a36ForSQTK_holds CFSG.Quasithin.a38ForSQTK_proved)
    (CFSG.Quasithin.H13.U3.stmt13_3_8_holds h13.stmt13_3_2)
    (CFSG.Quasithin.H13.U3.stmt13_2_2_9L1_of_cases
      (CFSG.Quasithin.H13.U3.stmt13_2_2_9L1Nat_holds h13.stmt13_3_2)
      (CFSG.Quasithin.H13.U3.stmt13_2_2_9L1Perm_holds h13.stmt13_3_2))
  have hAut : CFSG.Quasithin.H13.A6.Fact13820Aut :=
    CFSG.Quasithin.H13.A6.fact13820Aut_of CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
      h1339 (CFSG.Quasithin.H13.U3.stmt13_3_4_of h13.stmt13_3_2)
      (CFSG.Quasithin.H13.A6.lem13813_holds h13.stmt13_3_14 h13315
        (CFSG.Quasithin.H13.A6.input1356Two_of h1222
          (CFSG.Quasithin.H13.A6.input1356TwoS6_of_hubs h1222 h13315))
        h1339)
      CFSG.Quasithin.H13.A6.autBorel13820L2_holds CFSG.Quasithin.H13.A6.autBorel13820L3_holds
      CFSG.Quasithin.Background.Harris.AutBorel.autBorel13820U3_holds
      CFSG.Quasithin.Background.Harris.AutBorel.autBorel13820Sp4_holds
      CFSG.Quasithin.H13.A6.autBorel13820G2_holds
  have h1381 : CFSG.Quasithin.H13.Stmt13_8_1 :=
    CFSG.Quasithin.H13.A6.stmt13_8_1_of_root5gW_A5 h331 h13.stmt13_3_2 h1222
      h08.stmt12_2_13 h13315 h03 h132 CFSG.Quasithin.MS93.c134Weak_holds hC137 h11.sliceA5
      h12.j4TwoLocals h13316 h13.stmt13_4_1 h14.input13721K h13828 hAut
      h14.case13821Hat6 h14.case13821HatM22 h14.case13821L32Hat
  have hZ437 : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z :=
    CFSG.Quasithin.H13.Ch4.gap437Sp4Z_of CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds
      (CFSG.Quasithin.H13.Ch4.lemmaC53C56Six_of CFSG.Quasithin.theoremC126_proved
        CFSG.Quasithin.C58NS.minParabolicBlockSubnormal_holds)
      CFSG.Quasithin.a37ForSQTK_proved CFSG.Quasithin.a38ForSQTK_proved
      CFSG.Quasithin.a39ForSQTK_proved
  have h14813 : CFSG.Quasithin.H13.Stmt14_8_1_three :=
    CFSG.Quasithin.H13.stmt14_8_1_three_of_openW_slices h331 h1222 h08.stmt12_2_13
      h13.stmt13_3_2 h1352 h1381 h132 hC137
      CFSG.Quasithin.H13.goldschmidtEdgeBoundS3_holds h12.i45 h11.sliceA5 h15.lemma14324
      h15.case1442 h15.lemma1449 h15.lemma14751 h03 h48 hZ437
  intro G _ _ T L hH hmax
  exact CFSG.Quasithin.H13.qt_h13_maximal_local_catalog_assembly_of_inputs h137 h1312 h13316
    h1361 h1381 h14813 G T L hH ⟨hmax, hH.faithful⟩

end CFSG.Yardstones.M64f425cd8476

end
