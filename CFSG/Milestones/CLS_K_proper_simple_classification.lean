module

public import CFSG.Assembly.Catalog
public import CFSG.Adapters.CatalogAgree
public import CFSG.FeitThompson.OddOrderTheorem
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
public import CFSG.Blueprint.NativeSporadic
public import CFSG.RankThree.PartOne.CTP.FusionSound
import CFSG.Sporadic.Bridge.BFusSevenGen
public import CFSG.YGroups.Y443.Native.CoverFactsWords
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Swap13Word
public import CFSG.Sporadic.Ly.FiveFacts
import CFSG.Sporadic.Ly.Certificate
public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs
import Certificates.Kernel.GammaU.BaseBridge
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBData
public import CFSG.YGroups.Y443.Native.Words
import Certificates.Kernel.KDenseP.MonSevenB
import Certificates.Kernel.KDenseP.MonSevenC
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import Certificates.Kernel.Co2Smith.Cox
import Certificates.Data.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Cox
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.CoxData
import Certificates.Kernel.Co2Smith.MarkK
public import Certificates.Data.TitsAschbacherFive
public import Certificates.Kernel.EvenBN.Bind
public import Certificates.Kernel.EvenBN.DWord
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.BasicCheck
import Certificates.Kernel.HN1408.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T1Facts
import Certificates.Kernel.G2Three.Sec1T1Glue
import Certificates.Data.Kernel.G2Three.Sec1T1
import Certificates.Kernel.G2Three.Sec1T1Rec
import CFSG.Certificates.Kernel.G2Three.Sec1Tab
import CFSG.Certificates.Kernel.Co1DceCover
import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef
import Certificates.Kernel.G2Three.Sec1T3Glue
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T5Facts
import Certificates.Kernel.G2Three.Sec1T5Glue
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
import Certificates.Kernel.E6RegPair.Assembly
public import CFSG.Assembly.ComponentType
public import CFSG.Assembly.Disconnected
public import CFSG.Assembly.LargeEven
public import CFSG.Assembly.Quasithin
public import CFSG.Assembly.RankThreeEven
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
