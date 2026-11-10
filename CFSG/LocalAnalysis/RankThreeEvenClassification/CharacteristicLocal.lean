module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoreTransport

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v


theorem pCore_map_le {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (prime : ℕ) (equivalence : G ≃* otherGroup) :
    (pCore prime G).map equivalence.toMonoidHom ≤ pCore prime otherGroup := by
  apply le_pCore_of_normal prime
  · exact (pCore_normal G prime).map equivalence.toMonoidHom equivalence.surjective
  · exact (pCore_isPGroup G prime).of_equiv (equivalence.subgroupMap (pCore prime G))

theorem pCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (prime : ℕ) (equivalence : G ≃* otherGroup) :
    (pCore prime G).map equivalence.toMonoidHom = pCore prime otherGroup := by
  apply le_antisymm (pCore_map_le prime equivalence)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  exact pCore_map_le prime equivalence.symm

theorem pCore_characteristic (G : Type u) [Group G] (prime : ℕ) :
    (pCore prime G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro equivalence
  exact pCore_map_equiv prime equivalence


end CFSG.RankThreeEvenClassification.Helpers
