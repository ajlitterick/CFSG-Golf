module

public import CFSG.Yardstones.M0ff270807621.Goals
import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Sporadic.Ly.GenSpecBase
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFacts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.FactsGen
public import CFSG.GH74.Generic.S45.LLinSel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7TwistMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma415Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import Certificates.Data.CatFactsL4U4P1U43Data

public section

universe u v w

namespace CFSG.Assembly.RankThreeEven

open Matrix in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.r3e_part_one_outcome_assembly
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : evenRank G = 3) (hq : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3) :
    IModel G ∨ AschCoreLocal G 2 :=
  CFSG.Yardstones.M0ff270807621.part_one_outcome_of_yardstones
    CFSG.Yardstones.M0ff270807621.r4CountPM_holds
    CFSG.Yardstones.M0ff270807621.r4EdgeFalse_holds
    CFSG.Yardstones.M0ff270807621.r4CentTwin_holds
    CFSG.Yardstones.M0ff270807621.r4TwistAllTwin_holds
    CFSG.Yardstones.M0ff270807621.r4SmallLeaves_holds
    CFSG.Yardstones.M0ff270807621.frameAEmptyP_holds
    CFSG.Yardstones.M0ff270807621.thmCThinE8E64E29_holds
    CFSG.Yardstones.M0ff270807621.thmCAE_holds
    CFSG.Yardstones.M0ff270807621.thmD2Leaves_holds
    CFSG.Yardstones.M0ff270807621.twinConnCoreInputs_holds
    CFSG.Yardstones.M0ff270807621.twinDiscPerpSPAll_holds
    CFSG.Yardstones.M0ff270807621.twinPerpSEAll_holds
    CFSG.Yardstones.M0ff270807621.model1524Twin3Om_holds
    CFSG.Yardstones.M0ff270807621.linkZ2L2Leaves_holds
    CFSG.Yardstones.M0ff270807621.linkEdgeRigidAll_holds
    (fun G _ _ _ hnab hrank hsect =>
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnab hrank hsect)
    G hnonab hK hchar he hq

end CFSG.Assembly.RankThreeEven
