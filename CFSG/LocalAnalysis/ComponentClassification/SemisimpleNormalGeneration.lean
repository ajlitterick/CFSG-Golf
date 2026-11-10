module

public import CFSG.LocalAnalysis.ComponentClassification.LocalBNormalGeneration
public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleLocalContainment

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SemisimpleNormalGeneration

theorem layer_eq_normalClosure_eq_derived_of_containment {G : Type*} [Group G]
    (element : G) (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hcontained : perfectSubgroup ≤ Layer.subgroup G)
    (hcover : Subgroup.normalClosure (perfectSubgroup : Set G) ⊔ Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = Subgroup.normalClosure (perfectSubgroup : Set G) ∧
      Subgroup.normalClosure (perfectSubgroup : Set G) = commutator G := by
  let normalClosure := Subgroup.normalClosure (perfectSubgroup : Set G)
  let : (Layer.subgroup G).Normal := Layer.normal G
  let : Group.IsPerfect normalClosure := LocalBNormalGeneration.perfect_normalClosure perfectSubgroup
  have hclosureLayer : normalClosure ≤ Layer.subgroup G := Subgroup.normalClosure_le_normal hcontained
  have hclosureDerived : normalClosure = commutator G := by
    apply le_antisymm
    · calc
        normalClosure = ⁅normalClosure, normalClosure⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator G := rfl
    · exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hcover inferInstance
  exact ⟨le_antisymm ((Layer.le_derived G).trans hclosureDerived.ge) hclosureLayer,
    hclosureDerived⟩


end CFSG.ComponentClassification.SemisimpleNormalGeneration
