module

public import CFSG.Milestones.CTB_KProper_component_local_B
public import CFSG.Open.CTInitialFrontierTauCeti
import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Sporadic.Ly.GenSpecBase
import CFSG.Sporadic.Ly.TwoWeightsSpecBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyHHBase
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443

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
