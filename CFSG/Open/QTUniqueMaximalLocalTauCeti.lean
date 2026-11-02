module

public import CFSG.Assembly.QuasithinDefs
public import CFSG.Milestones.QT_unique_maximal_local_classification
public import CFSG.Open.QTFaithfulEmptyTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Sporadic.J4.QT2LocX0Native
public import Certificates.Data.CFSGNative.J4.PentScan
import Certificates.Kernel.J4Q.QTBase

public section

namespace CFSG.Open.QTUniqueMaximalLocalTauCeti

open CFSG.Assembly CFSG.Assembly.Quasithin CFSG.Open.QTFaithfulEmptyTauCeti

theorem qt_unique_maximal_local_classification_of_agree
    (hB : CatalogAgree)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : quasithinIsQTKE G) (T : Sylow 2 G)
    (hT : ∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) :
    InCatalog G :=
  (hB G hnonab).2 (Milestones.qt_unique_maximal_local_classification G hnonab
    (quasithinIsQTKECat_of_agree hB hqtke) T hT)

end CFSG.Open.QTUniqueMaximalLocalTauCeti
