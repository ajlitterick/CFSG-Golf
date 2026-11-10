module

public import CFSG.Assembly.RankThreeEven
import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Sporadic.Ly.GenSpecBase
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
import Certificates.Kernel.Misc.E6StdSlp
import CFSG.Sporadic.Bridge.BFusSevenGen
import Certificates.Kernel.KDense.Y443
import Certificates.Kernel.E6RegPair.Assembly
import CFSG.Certificates.Kernel.E6RegPairSound

public section

universe u v w

namespace CFSG.Assembly

open Matrix in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cls_rank_three_even_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : evenRank G = 3) : InCatalog G :=
  _root_.CFSG.Assembly.rank_three_even G hnonab hK hchar he

end CFSG.Assembly
