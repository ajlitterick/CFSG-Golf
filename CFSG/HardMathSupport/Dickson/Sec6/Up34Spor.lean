module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.Down
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co1
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co2
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co3
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi23
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.HN
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.J4
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Ly
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.McLON
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Suz
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Two
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThree
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFi22Five
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo3
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporFi22
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporJ3
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporLy
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporSuz
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.FixCount
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24Tc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEHj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.Sporadic.Co1Block.TwoBTri
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.Ly.ThreeBSpec
public import CFSG.Sporadic.Recognition.LyonsAS44Quat
public import CFSG.Sporadic.Recognition.LyonsLocalEdge
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import Certificates.Data.Fi22PairSize
public import Certificates.Data.PtOrbit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

structure Up34SporRest : Prop where
  Fi24Prime : SporL34Free .Fi24Prime
  B : SporL34Free .B
  M : SporL34Free .M

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 in
theorem up34SporLeaf_of_rest (hrest : Up34SporRest) : Up34SporLeaf := by
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  refine up34SporLeaf_of_free CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds ?_
  intro name
  cases name
  case M11 => exact sporL34Free_of_down (sporL3DownInner_M11 hbr)
  case M12 => exact sporL34Free_of_down (sporL3DownInner_M12 hbr)
  case M22 => exact sporL34Free_of_down (sporL3DownInner_M22 hbr)
  case M23 => exact sporL34Free_of_down (sporL3DownInner_M23 hbr)
  case M24 => exact sporL34Free_of_down (sporL3DownInner_M24 hbr)
  case J1 => exact sporL34Free_of_down (sporL3DownInner_J1 hbr)
  case J2 => exact sporL34Free_of_down (sporL3DownInner_J2 hbr)
  case J3 => exact sporL34Free_of_down (sporL3DownInner_J3 hbr)
  case J4 => exact sporL34Free_of_down (sporL3DownInner_J4 hbr)
  case Co1 => exact sporL34Free_of_down (sporL3DownInner_Co1 hbr)
  case Co2 => exact sporL34Free_of_down (sporL3DownInner_Co2 hbr)
  case Co3 => exact sporL34Free_of_down (sporL3DownInner_Co3 hbr)
  case Fi22 => exact sporL34Free_of_down (sporL3DownInner_Fi22 hbr)
  case Fi23 => exact sporL34Free_of_down (sporL3DownInner_Fi23 hbr)
  case Fi24Prime => exact hrest.Fi24Prime
  case HN => exact sporL34Free_of_down (sporL3DownInner_HN hbr)
  case HS => exact sporL34Free_of_down (sporL3DownInner_HS hbr)
  case He => exact sporL34Free_of_down (sporL3DownInner_He hbr)
  case Ly => exact sporL34Free_of_down (sporL3DownInner_Ly hbr)
  case McL => exact sporL34Free_of_down (sporL3DownInner_McL hbr)
  case ONan => exact sporL34Free_of_down (sporL3DownInner_ONan hbr)
  case Ru => exact sporL34Free_of_down (sporL3DownInner_Ru hbr)
  case Suz => exact sporL34Free_of_down (sporL3DownInner_Suz hbr)
  case Th => exact sporL34Free_of_down (th_sporL3DownInner hbr)
  case B => exact hrest.B
  case M => exact hrest.M

end CFSG.HardMathSupport.Dickson.Sec6
