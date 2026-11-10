module

public import CFSG.Open.QTUniqueMaximalLocalTauCeti
public import CFSG.Adapters.CatalogAgree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Sporadic.J4.QT2LocX0Native
public import Certificates.Data.CFSGNative.J4.PentScan
import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.YGroups.DCE.B433Check
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.Open.QTFaithfulEmptyTauCeti

open CFSG.Assembly CFSG.Assembly.Quasithin

theorem qt_faithful_local_empty_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : Assembly.Quasithin.quasithinIsQTKE G)
    (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
        Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G, ¬ Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    InCatalog G :=
  qt_faithful_local_empty_classification_of_agree catalogAgree G hnonab hqtke T hMT hLf

end CFSG.Open.QTFaithfulEmptyTauCeti

namespace CFSG.Open.QTUniqueMaximalLocalTauCeti

open CFSG.Assembly CFSG.Assembly.Quasithin CFSG.Open.QTFaithfulEmptyTauCeti

theorem qt_unique_maximal_local_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : Assembly.Quasithin.quasithinIsQTKE G)
    (T : Sylow 2 G)
    (hT : ∃! M : Subgroup G, Assembly.Quasithin.quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) :
    InCatalog G :=
  qt_unique_maximal_local_classification_of_agree catalogAgree G hnonab hqtke T hT

end CFSG.Open.QTUniqueMaximalLocalTauCeti
