module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.GeneratedCore

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem subgroup_map_equiv_symm {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup) (subgroup : Subgroup G) :
    (subgroup.map equivalence.toMonoidHom).map equivalence.symm.toMonoidHom = subgroup := by
  have hcomposition : equivalence.symm.toMonoidHom.comp equivalence.toMonoidHom =
      MonoidHom.id G := by
    ext element
    exact equivalence.symm_apply_apply element
  rw [Subgroup.map_map, hcomposition, Subgroup.map_id]

theorem centralizer_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup) (subgroup : Subgroup G) :
    (Subgroup.centralizer (subgroup : Set G)).map equivalence.toMonoidHom =
      Subgroup.centralizer (subgroup.map equivalence.toMonoidHom : Set otherGroup) := by
  ext element
  constructor
  · intro hmem
    obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hmem
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨otherPreimage, hotherPreimage, rfl⟩ := Subgroup.mem_map.mp hother
    rw [← map_mul, ← map_mul]
    exact congrArg equivalence (Subgroup.mem_centralizer_iff.mp hpreimage
      otherPreimage hotherPreimage)
  · intro hmem
    apply Subgroup.mem_map.mpr
    refine ⟨equivalence.symm element, ?_, equivalence.apply_symm_apply element⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    apply equivalence.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hmem (equivalence other)
      (Subgroup.mem_map_of_mem equivalence.toMonoidHom hother)


end CFSG.RankThreeEvenClassification.Helpers
