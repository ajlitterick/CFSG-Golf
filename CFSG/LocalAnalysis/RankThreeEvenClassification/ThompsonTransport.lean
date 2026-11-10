module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonFoundations
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonCanonical
import CFSG.Foundations.MaxOrderThompson

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v


theorem MaximumOrderAbelian.map_equiv {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) (subgroup : Subgroup G) (hmaximum : MaximumOrderAbelian subgroup) :
    MaximumOrderAbelian (subgroup.map equivalence.toMonoidHom) :=
  CFSG.map_mem_maxOrderAbelianFamily equivalence hmaximum


theorem thompsonOrderCenter_map_equiv {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) : (thompsonOrderCenter G).map equivalence.toMonoidHom = thompsonOrderCenter H := by
  rw [thompsonOrderCenter_eq_orderZJ, thompsonOrderCenter_eq_orderZJ]
  exact CFSG.map_orderZJ equivalence


end CFSG.RankThreeEvenClassification.Helpers
