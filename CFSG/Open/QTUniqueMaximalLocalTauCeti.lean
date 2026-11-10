module

public import CFSG.Milestones.QT_unique_maximal_local_classification
public import CFSG.Open.QTFaithfulEmptyTauCeti

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
