module

public import CFSG.Assembly.Catalog
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

namespace CFSG.Assembly

theorem _root_.CFSG.Milestones.cls_characteristic_two_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hchar : IsCharTwoType G) : InCatalog G :=
  charTwo_classification InCatalog quasithin rank_three_even large_even G hnonab hK hchar

end CFSG.Assembly
