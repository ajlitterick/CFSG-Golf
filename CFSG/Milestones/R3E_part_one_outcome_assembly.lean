module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Yardstones.M0ff270807621.Assembly
public import CFSG.Yardstones.M0ff270807621.Goals
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.Sporadic.Schreier.LyCheckSep
public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.He.FpSpec
import Certificates.Kernel.SporSch.Ly.SepGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Sporadic.J4.QT2LocX0Native
public import Certificates.Data.CFSGNative.J4.PentScan
import Certificates.Kernel.J4Q.QTBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
public import CFSG.Sporadic.Ly.Setup
import CFSG.Sporadic.Ly.GenSpecBase
public import CFSG.GroupTheory.TwoWeightData
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
public import CFSG.Monster.Existence.StdOdd.Defs
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.B.Classical.E6AdjointGroup
import Certificates.Kernel.Misc.E6StdSlp
public import CFSG.YGroups.Y443.Native.CoverFactsWords
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Swap13Word
public import CFSG.Sporadic.Ly.FiveFacts
import CFSG.Sporadic.Ly.Certificate
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
