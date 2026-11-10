module

import CFSG.LocalAnalysis.ComponentClassification.RankTwoFrontierFinal
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.ThompsonOrderFormula
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensusW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjWS
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
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
public import CFSG.Monster.B.TwoA.Census.CosetEnum
public import CFSG.Monster.Existence.Census.FusionGens
public import CFSG.Quasithin.Recognition.M12AscFive
public import CFSG.Quasithin.Recognition.M12AscY3
public import CFSG.RankThree.Native.HSMcLSmallCheck
public import CFSG.RankThree.PartOne.KS.OrbitCert
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Co1.Cover.Checks
public import CFSG.Sporadic.Co2Schreier.ThirdNode
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.Timmesfeld.Moufang.A6
public import CFSG.Timmesfeld.Moufang.Cases
public import CFSG.Timmesfeld.Moufang.J2Check
public import CFSG.Timmesfeld.Moufang.J2MatCheck
public import CFSG.Timmesfeld.Moufang.Three
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

universe u v w

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Open

theorem _root_.CFSG.Milestones.ct_rank_two_standard_recognition_frontier_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hrank : 2 ≤ pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (Blueprint.NativeSporadic.IsSporadic G .J2 ∨ Blueprint.NativeSporadic.IsSporadic G .Suz ∨
        Blueprint.NativeSporadic.IsSporadic G .He ∨ Blueprint.NativeSporadic.IsSporadic G .Ru ∨
        Blueprint.NativeSporadic.IsSporadic G .Co1) :=
  CFSG.ComponentClassification.RankTwoStandard.ct_rank_two_standard_recognition_models
    G hnonab hK L hL hrank

end CFSG.Open
