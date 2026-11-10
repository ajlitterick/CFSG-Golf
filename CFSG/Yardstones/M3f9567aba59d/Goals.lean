module

import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoOrthRouteHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFourHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourNonsplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFiveNonsplitHolds

public import CFSG.Yardstones.M3f9567aba59d.Definitions
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoSpPairHolds
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIRemaining
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryKRankFiveClose
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRemainingHolds
public import CFSG.Holt.H78.Bridge
public import CFSG.Holt.H78.Theorem1
public import CFSG.LieType.SeitzGeneration.SeitzStatus
import CFSG.LocalAnalysis.StandardType.GGRemStdSubTableBOpen
import CFSG.LocalAnalysis.StandardType.GGRemStdSubTableBHolds
import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCentHolds
import CFSG.LocalAnalysis.StandardType.GGRootCentStructKGInputHolds
import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcFlatHolds
import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverKnown
import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftKnown
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGNbrFrameNine
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagProof
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrTableBSymp
import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrthPlus
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBCard
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcOrder
import CFSG.LocalAnalysis.StandardType.GGExcCompLiftRestInputProof
import CFSG.LocalAnalysis.StandardType.GGSporKBMFree
import CFSG.LocalAnalysis.StandardType.GGSporKRestClose
import CFSG.LocalAnalysis.StandardType.GGSporKShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSyl
public import CFSG.Holt.CaseTwoBW
public import CFSG.Holt.OddCoreTwoGroupBasic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG.StandardType

theorem ggRemainderStdSubTableB_holds :
    GGRemainderStdSubTableB :=
  CFSG.StandardType.ggRemainderStdSubTableB_proved

theorem ggRemainderTableBL_holds :
    GGRemainderTableBLRest :=
  CFSG.StandardType.SmallExc.F4Two.ggF4TwoThreeCCentInput_holds

theorem ggRemainderCoxeterLabel_holds :
    GGRemainderCoxeterLabel :=
  CFSG.StandardType.ggResMultiNodeRestThreeKUnitaryQGeFourFieldTwoInput_holds

theorem ggRemainderSecFiveWeyl_holds :
    GGRemainderSecFiveWeyl := by
  exact ⟨CFSG.StandardType.ggSecFiveBCoordBCornerDenseInput_holds,
    CFSG.StandardType.ggSecFiveBCoordBOffQTwoOrthRouteInput_holds,
    CFSG.StandardType.ggSecFiveBCoordBUniFourInput_holds,
    CFSG.StandardType.ggSecFiveBCoordBSparseTwDFourSplitInput_holds,
    CFSG.StandardType.ggSecFiveBCoordBSparseTwDFourNonsplitInput_holds,
    CFSG.StandardType.ggSecFiveBCoordBSparseTwDFiveNonsplitInput_holds,
    CFSG.StandardType.ggSecFiveBPermProperQTwoSpPairMpInput_holds⟩

theorem ggRemainderSecFiveTypeA_holds :
    GGRemainderSecFiveTypeA :=
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hCD : GGTypeACompatDiagBInput := ggTypeACompatDiagBInput_of_known ggInnerDiagMpInput_holds hLB
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hF : GGNbrFrameInput := ggNbrFrameInput_of_one ggNbrFrameInputOne_holds
  have hTBwE : GGNbrTableBWeylInputOn fun p lab => lab.tag = .E6 ∧ p = 3 :=
    ggNbrTableBWeylInputOn_e6Three_holds
  have hTBoE : GGNbrTableBOrderRestInputOn fun p lab => lab.tag = .E6 ∧ p = 3 :=
    ggNbrTableBOrderRestInputOn_e6Three_holds
  have hTBwR : GGNbrTableBWeylInputOn fun _ lab =>
      ¬ lab.tag = .A ∧ ¬ lab.tag = .B ∧ ¬ lab.tag = .C ∧ ¬ lab.tag = .D :=
    ggNbrTableBWeylInputOn_exc_holds.of_cover hTBwE fun p lab h =>
      (Classical.em (lab.tag = .E6 ∧ p = 3)).symm.imp
        (fun hE => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hE⟩) id
  have hTBwDR : GGNbrTableBWeylInputOn fun _ lab =>
      ¬ lab.tag = .A ∧ ¬ lab.tag = .B ∧ ¬ lab.tag = .C :=
    ggNbrTableBWeylInputOn_typeD_holds.of_cover hTBwR fun _ lab h =>
      (Classical.em (lab.tag = .D)).imp id fun hD => ⟨h.1, h.2.1, h.2.2, hD⟩
  have hTB : GGNbrTableBWeylInput :=
    ggNbrTableBWeylInput_of_on ggNbrTableBWeylInputOn_typeA_holds
      (ggNbrTableBWeylInputOn_typeBC_holds.of_cover hTBwDR fun _ lab h =>
        (Classical.em (lab.tag = .B ∨ lab.tag = .C)).imp id
          fun hBC => ⟨h, fun hB => hBC (Or.inl hB), fun hC => hBC (Or.inr hC)⟩)
  have hTBoR : GGNbrTableBOrderRestInputOn fun _ lab => ¬ lab.tag = .C ∧ ¬ lab.tag = .D :=
    ggNbrTableBOrderRestInputOn_exc_holds.of_cover hTBoE fun p lab h =>
      (Classical.em (lab.tag = .E6 ∧ p = 3)).symm.imp (fun hE => ⟨h.1, h.2, hE⟩) id
  have hO : GGNbrTableBOrderRestInput :=
    ggNbrTableBOrderRestInput_of_on ggNbrTableBOrderRestInputOn_typeC_holds
      (ggNbrTableBOrderRestInputOn_typeD_holds.of_cover hTBoR fun _ lab h =>
        (Classical.em (lab.tag = .D)).imp id fun hD => ⟨h, hD⟩)
  have hC : GGNbrTableBCardInput := ggNbrTableBCardInput_holds
  And.intro
    (fun G _ _ p B Bs x L D J n f y K h hTP y' K' hK' hout =>
      ggTypeAReflOver_of_known hCD hLB hRig hTB hC hO hF h hTP hK' hout)
    (And.intro (ggTypeACrossLiftInput_of_known hCD hLB) ggNbrFrameInputOne_holds)

theorem ggRemainderSecFiveHalfSp_holds
    : GGRemainderSecFiveHalfSp := by
  exact ⟨⟨CFSG.StandardType.ggE6ThreeI1Rank_holds,
    CFSG.StandardType.GGK0ExcB3Prod.ggK0ExcB3_holds⟩,
    CFSG.StandardType.ggFieldTwoCornerNoSL28_holds⟩

theorem ggRemainderCorFiveTwenty_holds : GGRemainderCorFiveTwenty := by
  trivial

theorem ggRemainderStepOneExc_holds :
    GGRemainderStepOneExc :=
  And.intro CFSG.StandardType.LangRat.ggE7NonsplitCoreRestInput_holds
    CFSG.StandardType.LangRat.ggE8NonsplitCoreRestInput_holds

theorem ggRemainderStepOneConfig_holds :
    GGRemainderStepOneConfig :=
  CFSG.StandardType.RCKC1.rckRowK2IIIAtTwoRemaining_holds

theorem ggRemainderStepTwo_holds :
    GGRemainderStepTwo :=
  CFSG.StandardType.ggKGroupFusionAtFlatK_sporadic_of_halves
    CFSG.StandardType.SporadicShape.ggKGroupFusionAtFlatK_BM_free
    CFSG.StandardType.SporadicShape.ggKGroupFusionAtFlatK_rest_closed

theorem ggRemainderRootCentralizer_holds :
    GGRemainderRootCentralizer :=
  And.intro CFSG.StandardType.ggRootCentStructKGInput_holds
    CFSG.StandardType.ggRootCentAutKNotExcFlatInput_holds

theorem ggRemainderStepThreeExc_holds :
    GGRemainderStepThreeExc := by
  trivial

theorem kFactSeitzRankTwo_holds :
    CFSG.AGLEmbeddingD2.KFactSeitzRankTwo :=
  CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds

theorem holtUniqueFixedPointSimple_holds :
    CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple :=
  CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1

end CFSG.Yardstones.M3f9567aba59d
