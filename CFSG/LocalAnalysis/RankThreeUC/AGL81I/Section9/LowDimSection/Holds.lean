module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Main
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.GLTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.GLThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.SpFour
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Out
public import CFSG.Quasithin.Background.DicksonPerfectPSL2
public import CFSG.RankThree.PartOne.KF.BloomClose
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL
public import CFSG.RankThree.SubgroupLists.MitchellQuasisimple
public import CFSG.RankThree.SubgroupLists.MitchellPartThreeProof
public import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
public import CFSG.RankThree.SubgroupLists.SymplecticFischerUnitary
public import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalGroups
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.B433Check
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem lowDimMulAutSection_holds :
    LowDimMulAutSection :=
  lowDimMulAutSection_of
    (gLTwoLowDimSections_of fun _ _ hp2 L =>
      (CFSG.Quasithin.Dickson.dickson_prime_cases hp2 L).imp_right (Or.imp_right And.left))
    (gLThreeQuasisimpleLowDim_of CFSG.RankThree.PartOne.extBloomMitchell_holds
      fun _ hG hne => CFSG.RankThree.PartTwo.Sec4.Census.eq_statedSL_of_isPerfect hG hne)
    (spFourQuasisimpleLowDim_of fun _ _ hp2 _ hGS hq =>
      CFSG.RankThree.SubgroupLists.mitchell_quasisimple_sp4_of
        CFSG.RankThree.SubgroupLists.mitchellPartThree_holds
        CFSG.RankThree.SubgroupLists.fischerSpClique CFSG.RankThree.SubgroupLists.fischerOrthClique
        CFSG.RankThree.SubgroupLists.fischerSpCard CFSG.RankThree.SubgroupLists.fischerOrthCard
        CFSG.RankThree.SubgroupLists.fischerUnitaryCard
        CFSG.RankThree.SubgroupLists.fischerReflectionCard hp2 hGS hq)
    (lowDimOutSolvable_of CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
      fun G _ t n p f h => CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G t n p f h)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
