module

public import CFSG.Quasithin.Vol2.Ch11SecWire11P
public import CFSG.Quasithin.Vol2.Ch11SecWire11X
public import CFSG.Quasithin.Vol2.Ch11SecWire11XW
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.CLSEvenE6AllInvolutionFourGroup
public import CFSG.LieType.Chevalley.CLSEvenTrialityFourGroup
public import CFSG.LieType.Chevalley.CLSOddTrialityAllInvolutionFourGroup
public import CFSG.LieType.Chevalley.CLSOddTwistedE6AllInvolutionFourGroup
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaInvolutionConjugacy
public import CFSG.LocalAnalysis.ComponentInitial.CLSEvenOrthogonalSemilinearFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.CLSSmallReeModelInvolutionsInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherEvenRankOneSmallModels
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticEvenAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.SteinbergCCExistingCLS
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.Quasithin.H13.A7Nat1238YCases
public import CFSG.Quasithin.H13.NQBlockOriginalRControlled
public import CFSG.Quasithin.H13.NQCoreCh1Statements
public import CFSG.Quasithin.H13.NQCoreP134
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.H13.NQRigidAsmSingle
public import CFSG.Quasithin.H13.NQTermTerminalFourWitness
public import CFSG.Quasithin.H13.QTESylowThreeNative
public import CFSG.Quasithin.Vol2.Ch11SecWire11HW
public import CFSG.Quasithin.Vol2.Ch11SecWire11JW
public import CFSG.Quasithin.Vol2.Ch11SecWire11KW
public import CFSG.Quasithin.Vol2.Ch11SecWire11LW
public import CFSG.Quasithin.Vol2.Ch11SecWire11MW
public import CFSG.Quasithin.Vol2.Ch11SecWire11NW
public import CFSG.Quasithin.Vol2.Ch11SecWire11WW
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch4Sec3L43Q517
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Z
public import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.OddKernel.EightGroupDims
public import CFSG.RankThree.OddKernel.SporadicKernelCases
public import CFSG.RankThree.PartOne.S10.CyclicSemisimpleSectionOrbit
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Co1.Cover.Rels
public import CFSG.Sporadic.Recognition.J4MultiplierFox
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.Vol2.Ch11

theorem stmt11_0_1_of_remainingW
    (hIn : Inputs11_0_1W) (h10 : H13.Stmt10_0_1) (h1 : Open11_1) :
    H13.Stmt11_0_1 := by
  have h : Wire11.PartsW :=
    ⟨hIn, h10, h1, Wire11.proved⟩
  have h11_0_0 := Wire11.stmt11_0_0W h
  have hTmpL6_3_2_2_six := Wire11.tmpL6_3_2_2_sixW h
  have h3_2_5 := Wire11.stmt3_2_5W h hTmpL6_3_2_2_six
  have h11_0_2 := Wire11.stmt11_0_2W h h3_2_5
  have h11_0_3 := Wire11.stmt11_0_3W h hTmpL6_3_2_2_six h3_2_5 h11_0_2
  have h11_1_0 := Wire11.stmt11_1_0 h11_0_2 h11_0_3
  have hTmpL6_4_2_13 := Wire11.tmpL6_4_2_13W h
  have h11_0_4 := Wire11.stmt11_0_4W h h11_0_2
  have h11_1_1 := Wire11.stmt11_1_1W h h11_0_2
  have h11_1_2Star := Wire11.stmt11_1_2StarW h h3_2_5 h11_0_2 h11_0_3 h11_1_0 hTmpL6_4_2_13
  have h11_1_2 := Wire11.stmt11_1_2W h h11_0_2 h11_0_3 h11_1_1 h11_1_2Star
  have h11_1_3 := Wire11.stmt11_1_3W h h11_0_2 h11_0_3 h11_1_2
  have h11_1_4 := Wire11.stmt11_1_4W h h11_0_2 h11_1_0 h11_1_3
  have h11_1_2RadU := Wire11.stmt11_1_2RadUW h h11_0_2 h11_0_3 h11_1_1
  have h11_2_2 := Wire11.stmt11_2_2W h h11_0_2 h11_0_3 hTmpL6_4_2_13 h11_0_4 h11_1_3 h11_1_4
      h11_1_2RadU
  have h11_2_4 := Wire11.stmt11_2_4W h h11_0_2 h11_0_3 h11_1_3 h11_2_2
  have h11_2_5 := Wire11.stmt11_2_5W h h11_2_4
  have h11_1_5 := Wire11.stmt11_1_5W h h11_0_2 h11_0_3 h11_1_0 hTmpL6_4_2_13 h11_0_4
  have h11_2_3 := Wire11.stmt11_2_3W h h11_0_2 h11_1_0 h11_1_2 h11_1_5
  have h11_3_3 := Wire11.stmt11_3_3W h h11_0_2 h11_0_3 h11_2_2 h11_2_5 h11_2_3
  have hE114OneResRest := Wire11.e114OneResRest
  have hE114OneRes := Wire11.e114OneRes hE114OneResRest
  have hE114ForE22R := Wire11.e114ForE22RW h hE114OneRes
  have hE22StatementC := Wire11.e22StatementCW h hE114ForE22R
  have hDerivedHallBorel := Wire11.derivedHallBorel hE22StatementC
  have hTmpL4_4_2 := Wire11.tmpL4_4_2W h
  have h11_2_1 := Wire11.stmt11_2_1W h h11_0_2 h11_0_3 hE22StatementC hDerivedHallBorel hTmpL4_4_2
  have h11_3_4 := Wire11.stmt11_3_4W h h11_0_2 h11_0_3 h11_1_0 h11_2_2 h11_2_3 h11_3_3 h11_2_1
  have h11_3_5 := Wire11.stmt11_3_5W h h3_2_5 h11_0_2 h11_0_3 h11_0_4 h11_2_2 h11_2_3 h11_3_3
      hE22StatementC hDerivedHallBorel hTmpL4_4_2 h11_2_1
  have h11_3_6 := Wire11.stmt11_3_6W h h11_0_2 h11_0_3 h11_0_4 h11_2_2 h11_2_3 h11_3_3 h11_2_1
      h11_3_5
  have h11_3_7 := Wire11.stmt11_3_7W h h11_0_2 h11_0_4 h11_2_2 h11_3_4 h11_3_5 h11_3_6
  have h11_3_2 := Wire11.stmt11_3_2W h h11_0_2 h11_3_3 h11_3_4 h11_3_5 h11_3_6 h11_3_7
  have h11_4_1 := Wire11.stmt11_4_1W h h11_0_0 h11_0_2 h11_0_3 h11_1_0 h11_1_1 h11_1_2 h11_2_2
      h11_3_2
  have h11_4_2 := Wire11.stmt11_4_2W h h3_2_5 h11_0_2 h11_0_3 h11_1_0 h11_0_4 h11_1_1 h11_1_5 h11_3_2
      h11_4_1
  have h11_4_3 := Wire11.stmt11_4_3W h h11_0_2 h11_1_0 h11_1_1 h11_1_2 h11_2_3 h11_3_2 h11_4_1
      h11_4_2
  have hAs_p778_nParamS := Wire11.as_p778_nParamSW h hE114OneResRest
  have h11_4_4S := Wire11.stmt11_4_4SW h h11_0_2 h11_0_3 h11_1_0 h11_0_4 h11_1_1 hTmpL4_4_2 h11_4_1
      h11_4_2
  have h11_5_1 := Wire11.stmt11_5_1W h h11_0_2 h11_1_0 h11_1_2 h11_2_2 h11_4_1 h11_4_3
      hAs_p778_nParamS h11_4_4S
  have h11_5_3 := Wire11.stmt11_5_3W h h11_0_2 h11_0_3 h11_1_0 h11_2_2 h11_2_5 h11_4_1 h11_4_2
      h11_4_3 hAs_p778_nParamS h11_4_4S h11_5_1
  have h11_5_4 := Wire11.stmt11_5_4 h11_0_2 h11_0_3 h11_1_0 h11_1_2 h11_2_3 h11_4_1 h11_4_3 h11_5_3
  have h11_5_5 := Wire11.stmt11_5_5 h11_0_2 h11_4_1 h11_5_1
  have h11_5_6 := Wire11.stmt11_5_6W h h11_0_2 h11_0_3 h11_1_0 h11_1_1 h11_1_2 h11_4_1 h11_4_3
      h11_5_1
  have h11_5_7SL3 := Wire11.stmt11_5_7SL3W h h11_0_2 h11_1_0 h11_1_1 h11_1_2 h11_4_1 h11_4_3 h11_5_4
      h11_5_5 h11_5_6
  have h11_5_7Sp4 := Wire11.stmt11_5_7Sp4W h h11_0_2 h11_0_3 h11_1_0 h11_1_2 h11_1_3 h11_1_4 h11_1_5
      h11_4_1 h11_4_3 h11_5_4 h11_5_5 h11_5_6
  have h11_5_7 := Wire11.stmt11_5_7 h11_5_1 h11_5_7SL3 h11_5_7Sp4
  have h11_5_8 := Wire11.stmt11_5_8W h h11_0_2 h11_1_0 h11_1_1 h11_1_2 h11_2_2 h11_4_1 h11_4_2
      h11_4_3 h11_5_1 h11_5_5 h11_5_6 h11_5_7
  exact Wire11.stmt11_0_1W h h11_0_0 h11_1_0 h11_5_3 h11_5_7 h11_5_8

theorem stmt11_0_1_of_openW
    (hIn : Inputs11_0_1W) (h1 : Open11_1) : H13.Stmt11_0_1 :=
  stmt11_0_1_of_remainingW hIn (Ch10.stmt10_0_1_of_remainingA hIn.in10) h1

end CFSG.Quasithin.Vol2.Ch11
