module

public import CFSG.LocalAnalysis.QuasithinUnique.TopNative

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
