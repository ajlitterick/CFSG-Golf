module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareBlock
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSymplectic
import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareUnitary
import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinPlus
import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinMinus
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
import CFSG.CGT.PushingUpLit.Statements
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Statements
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.PartTwo.Census.Spin.Main
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.StronglyEmbedded
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.SquareDispatch

theorem squareSpFamily_holds : SquareSpFamily :=
  fun _ _ _ _ _ _ _ _ e _ _ _ ρ hρ hρker h3 T J hNJ hJ hQ =>
    SquareSymplectic.three_le_pRank_sp e ρ hρ hρker h3 T J hNJ hJ hQ

theorem squareSUFamily_holds : SquareSUFamily :=
  fun _ _ _ _ _ _ hF hn _ _ _ e _ _ _ ρ hρ hρker h3 T J hNJ hJ hQ =>
    SquareUnitary.three_le_pRank_su hF hn e ρ hρ hρker h3 T J hNJ hJ hQ

theorem squareSpinPlusFamily_holds : SquareSpinPlusFamily :=
  fun _ _ _ _ _ hn _ _ _ e _ _ _ ρ hρ hρker h3 T J hNJ hJ hQ =>
    SquareSpinPlus.three_le_pRank_spinPlus hn e ρ hρ hρker h3 T J hNJ hJ hQ

theorem squareSpinMinusFamily_holds : SquareSpinMinusFamily :=
  fun _ _ _ _ _ _ _ hirr hn _ _ _ e _ _ _ ρ hρ hρker h3 T J hNJ hJ hQ =>
    SquareSpinMinus.three_le_pRank_spinMinus hirr hn e ρ hρ hρker h3 T J hNJ hJ hQ


theorem kFactBlockAltFiveSquareParabolic_holds : KFactBlockAltFiveSquareParabolic :=
  kFactBlockAltFiveSquareParabolic_of
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved)
    (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    squareSpFamily_holds squareSUFamily_holds squareSpinPlusFamily_holds
    squareSpinMinusFamily_holds

end CFSG.AGLEmbeddingD2
