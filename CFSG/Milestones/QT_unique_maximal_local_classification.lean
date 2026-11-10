module

public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.QuasithinUnique.TopNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Sporadic.J4.QT2LocX0Native
public import Certificates.Data.CFSGNative.J4.PentScan
import Certificates.Kernel.J4Q.QTBase

public section

namespace CFSG.Milestones

open CFSG.Assembly CFSG.Assembly.Quasithin

theorem qt_unique_maximal_local_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : QuasithinUnique.quasithinIsQTKECat G)
    (T : Sylow 2 G)
    (hT : ∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) :
    Blueprint.Catalog G := by
  exact CFSG.QuasithinUnique.qt_unique_maximal_local_classification_proved G hnonab hqtke T hT

end CFSG.Milestones
