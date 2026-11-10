module

public import CFSG.Assembly.LargeEven
import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Sporadic.Ly.GenSpecBase
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
import Certificates.Kernel.Misc.E6StdSlp
import CFSG.Sporadic.Bridge.BFusSevenGen
import Certificates.Kernel.KDense.Y443
import Certificates.Kernel.GammaU.BaseBridge
import Certificates.Kernel.KDenseP.MonSevenB
import Certificates.Kernel.KDenseP.MonSevenC
import Certificates.Kernel.E6RegPair.Assembly
import CFSG.Certificates.Kernel.E6RegPairSound

public section

universe u v w

namespace CFSG.Assembly

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cls_large_even_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) : InCatalog G :=
  _root_.CFSG.Assembly.large_even G hnonab hK hchar he

end CFSG.Assembly
