module

public import CFSG.Yardstones.M41b0c98b3153.Goals
public import CFSG.Yardstones.M41b0c98b3153.Reduction
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
public import CFSG.Blueprint.LieModelAPI
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.Orders.OddLieType
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.Goldschmidt.Steps.G36Setup
public import CFSG.Holt.TwoGroupsFocal
public import CFSG.LargeExtraspecial.S8CBFSect
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGraph
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutCard
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenFinal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClOmega
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClSp
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSUGraph
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartOne.S11d.OutExceptional

public section

namespace CFSG.Yardstones.M41b0c98b3153

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN

theorem ct_even_standard_residual_reduction_of_goals
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L)) :
    Blueprint.Recognition.Exact.EvenStandardResidual L :=
  ct_even_standard_residual_reduction_of_yardstones
    u5LinearCaseExclusion
    u5ProductCaseExclusion
    gomiU42Input
    gomiLemma1PInput
    u52UnitaryCaseExclusion
    u52LinearSmallCentralizerExclusion
    sp4SingleCommutatorExclusion
    sp4BothTrivialProductExclusion
    sp4BothTrivialOddFieldNoSwap
    g2FourCenterlessExclusion
    g2LargeCenterlessExclusion
    trialityD4TwoCenterlessExclusion
    trialityD4LargeCenterlessExclusion
    titsThm49FailureExclusion
    titsThm49StatementExclusion
    G hnonab hK L hL hcore S hS htype hexc

end CFSG.Yardstones.M41b0c98b3153
