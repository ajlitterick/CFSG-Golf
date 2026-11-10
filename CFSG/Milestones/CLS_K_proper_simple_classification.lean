module

public import CFSG.Assembly.Catalog
public import CFSG.Adapters.CatalogAgree
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

namespace CFSG.Assembly

theorem _root_.CFSG.Milestones.cls_k_proper_simple_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hK : KProper InCatalog G) : InCatalog G :=
  kProper_classification InCatalog
    (fun _ _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)
    abelian_simple disconnected_involution_graph low_two_rank component_dichotomy
    component_type quasithin rank_three_even large_even G hK

theorem _root_.CFSG.Milestones.cls_k_proper_simple_classification_catalog
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hK : KCore.KProperAllSimple Blueprint.Catalog G) : Blueprint.Catalog G := by
  have hKPresentation : KProper InCatalog G :=
    KCore.KProperAllSimple.kProperNonab inCatalog_isoInvariant
      (KCore.KProperAllSimple.mono_of_finite
        (fun X _ _ _ hX => CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog X hX) hK)
  exact CFSG.QuasithinUnique.B1.catalog_of_inCatalog
    CFSG.RankThree.PartOne.TCB.catalogBridgeFor_all G
    (CFSG.Milestones.cls_k_proper_simple_classification G hKPresentation)

end CFSG.Assembly
