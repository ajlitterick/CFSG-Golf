module

public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SimpleStructure


theorem quasisimple (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : IsQuasisimple G := by
  let : Group.IsPerfect G := ⟨Helpers.commutator_eq_top G hnonab⟩
  exact Quasisimple.simple_of_perfect G


theorem layer_eq_top (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) : Layer.subgroup G = ⊤ := by
  apply top_unique
  apply Layer.component_le
  exact ⟨le_rfl, .refl ⊤, Components.quasisimple_of_equiv Subgroup.topEquiv (quasisimple G hnonab)⟩


end CFSG.ComponentClassification.SimpleStructure
