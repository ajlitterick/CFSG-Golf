module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.CTB_KProper_component_local_B
public import CFSG.Open.CTInitialFrontierTauCeti
public import CFSG.RankThree.PartOne.TCB.Final
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
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Schreier.J1QT
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.Open.CTBKProperLocalBTauCeti

open CFSG.Assembly

theorem kProper_component_local_B_of_bridge
    (hbridge : CatalogImp InCatalog CFSG.Blueprint.Catalog)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hcomp : IsComponentType G) : oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  Milestones.ctb_kproper_component_local_b G hnonab
    (CTInitialFrontierTauCeti.kProper_catalog_of_bridge hbridge hK) hcomp

theorem kProper_component_local_B
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hcomp : IsComponentType G) : oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_bridge RankThree.PartOne.TCB.tauCetiCatalogBridge G hnonab hK hcomp

end CFSG.Open.CTBKProperLocalBTauCeti
