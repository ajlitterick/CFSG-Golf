module

public import CFSG.Assembly.Exhaustiveness
public import CFSG.Milestones.CLS_K_proper_simple_classification
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
import Certificates.Kernel.HN1408.Basic
import Certificates.Kernel.G2Three.Sec1T1Glue
import CFSG.Certificates.Kernel.Co1DceCover
import Certificates.Kernel.G2Three.Sec1T3Glue
import Certificates.Kernel.E6RegPair.Assembly
import CFSG.Certificates.Kernel.E6RegPairSound

public section

namespace CFSG.Milestones

theorem cfsg_exhaustiveness
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    Blueprint.Catalog G :=
  QuasithinUnique.B1.catalog_of_inCatalog RankThree.PartOne.TCB.catalogBridgeFor_all G
    (Assembly.section_induction Assembly.InCatalog
      (fun X _ _ _ hX => cls_k_proper_simple_classification X hX) G)

end CFSG.Milestones
