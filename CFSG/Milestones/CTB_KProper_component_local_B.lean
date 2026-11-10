module

import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Sporadic.Ly.GenSpecBase
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
import CFSG.LocalAnalysis.ComponentClassification.GSRedNoB2L
public import CFSG.Yardstones.Mfe5fcbbc9cd3.Goals
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Struct
public import Certificates.Data.ONanCMChain
import CFSG.Yardstones.Mfe5fcbbc9cd3.Definitions

public section

universe u v w

namespace CFSG.Assembly.ComponentType

theorem _root_.CFSG.Milestones.ctb_kproper_component_local_b
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper CFSG.Blueprint.Catalog G)
    (hcomp : IsComponentType G) : oddCore G = ⊥ ∧ LocalBProperty G :=
  CFSG.ComponentClassification.GSRedNoB2L.ctb_kproper_component_local_b_of_yardstonesGS
    CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models
    CFSG.Milestones.cl_lit_classical_involution_theorem_models
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys01_lemma39TwoDiscK2At_hub
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys02_quasisimpleSylowFourJoinedSCN
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys03_solomonQTwoDisconnectedSylowInvFor
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys04_solomon2An
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys05_altStdCyclicOddTwoFalse
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys06_swapMemberResidueNineExact
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys07_swapMemberResidueNineExoticT2
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys08_swapMemberResidueNineExoticT3
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys09_signalizerNineSixDihedralLocal
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys12_griessSolomonInput
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys13_footeMaximalUnbalancedInput
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys14_gs82CentXA10Transfer
    CFSG.Yardstones.Mfe5fcbbc9cd3.ys15_gs82Step2Fuse
    G hnonab hK hcomp

end CFSG.Assembly.ComponentType
