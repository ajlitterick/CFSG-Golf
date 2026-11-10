module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
public import CFSG.Monster.B.GSide.HInnerFusionY3
import CFSG.LocalAnalysis.EvenSmallLie.FrontierFinal
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3GapG1
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.Fischer.Polar.Facts
public import CFSG.GH74.ThompsonOrderFormula
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Gen
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerPoints
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
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
public import CFSG.Quasithin.Recognition.M12AscFive
public import CFSG.Quasithin.Recognition.M12AscY3
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.Walter.JRFacts
import CFSG.GH74.M12.Reductions
import CFSG.LieType.Chevalley.OddE6AllInvolutionComponents
import CFSG.LieType.Chevalley.OddTrialityAllInvolutionComponents
import CFSG.LieType.Chevalley.OddTwistedE6InnerInvolutionComponents
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.Quasithin.Background.Basic
import CFSG.Quasithin.H13.J4Core
import CFSG.RankThree.Native.PrimeLines
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.Sporadic.Fi22.FischerOpen
import CFSG.Sporadic.FischerOddCore.Basic
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.SmallActionData

public section

universe u v w

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Open

theorem _root_.CFSG.Milestones.ct_even_small_lie_standard_frontier_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hres : Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hbcd : Blueprint.Recognition.Exact.ResidualB L ∨ Blueprint.Recognition.Exact.ResidualC L ∨
      Blueprint.Recognition.Exact.ResidualD L) :
    Blueprint.Recognition.EvenSporadicOutcome G :=
  CFSG.EvenSmallLie.FrontierFinal.frontier_models_of_epsilonOne
    CFSG.EvenSmallLie.Child3.gapEpsilonOne G hnonab hK L hL hcore S hS htype hexc hres hbcd

end CFSG.Open
