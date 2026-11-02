module

public import CFSG.Assembly.RankThreeEven
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
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import Certificates.Kernel.Co2Smith.Cox
import Certificates.Data.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Cox
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.CoxData
import Certificates.Kernel.Co2Smith.MarkK
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
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
