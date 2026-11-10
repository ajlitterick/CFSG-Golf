module

public import CFSG.RankThree.PartOne.DichotomyFrontier
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.KS.FinalAll
public import CFSG.RankThree.PartOne.KS.ONPointwise
public import CFSG.RankThree.PartOne.KP.Main
public import CFSG.RankThree.PartOne.KE.FinalAssembly
public import CFSG.RankThree.PartOne.SPOR.Co1Planes
public import CFSG.RankThree.PartOne.KLR.Final
public import CFSG.RankThree.PartOne.KGD.TrialityFamily
public import CFSG.RankThree.PartOne.SPOR.HNPlane
public import CFSG.RankThree.PartOne.KS.PlaneLy
public import CFSG.RankThree.PartOne.KA5L.Final
import Certificates.Kernel.SporSch.Ly.SepGlue
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonDefs
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KE.CTCasesE6
public import CFSG.RankThree.PartOne.KE.CTCasesE7Cox
public import CFSG.RankThree.PartOne.KE.CTCasesE8
public import CFSG.RankThree.PartOne.KE.CTTwistedCases
public import CFSG.RankThree.PartOne.KS.HeSevenCheck
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Co1Block.TwoBCent
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.StronglyEmbedded.ParityCriterion
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartOne.Outcome

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem selectedPrimeDichotomy_of_remaining :
    SelectedPrimeDichotomy :=
  selectedPrimeDichotomy_of_open_families TCB.tauCetiCatalogBridge
    (original_sporadic_component_local_core_odd_action_of_plane_inputs_and_on
        ⟨SPOR.sporadicPlaneOdd_Co1, SPOR.sporadicPlaneOdd_HN, sporadicPlaneOdd_Ly⟩
        ONPw.onPointwiseSeven_holds)
    (KE.original_exceptional_component_local_core_odd_action_of_open ⟨⟩ ⟨⟩ ⟨KA5L.a5Layer_E7⟩ ⟨⟩
      KD4L.d4TrialityLayer_E8 KD4L.d4TranspositionLayer_E8
      KGD.triality_family KLR.largeRee_all_actors)
    (original_coprime_catalog_component_local_core_centralization_of_B_section
        SPOR.sporadicCoprimeRankData_holds sectionsForceEvenRankFour_B
        simplePresentationMHasBSection_holds)

end CFSG.RankThree.PartOne.Outcome
