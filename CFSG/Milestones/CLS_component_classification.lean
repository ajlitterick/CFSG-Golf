module

public import CFSG.Assembly.ComponentType
import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Sporadic.Ly.GenSpecBase
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
import Certificates.Kernel.HN1408.Basic
import Certificates.Kernel.G2Three.Sec1T1Glue
import CFSG.Certificates.Kernel.Co1DceCover
import Certificates.Kernel.G2Three.Sec1T3Glue

public section

universe u v w

namespace CFSG.Assembly

theorem _root_.CFSG.Milestones.cls_component_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hrank : 3 ≤ twoRank G)
    (hcomp : IsComponentType G) : InCatalog G :=
  _root_.CFSG.Assembly.component_type G hnonab hK hrank hcomp

end CFSG.Assembly
