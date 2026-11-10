module

public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentAction

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem perfect_three_subgroup_action (L X : Subgroup G) [Group.IsPerfect L]
    (h : ⁅⁅X, L⁆, L⁆ = ⊥) : ⁅X, L⁆ = ⊥ := by
  rw [Subgroup.commutator_comm X L] at h ⊢
  exact Quasisimple.perfect_double_commutator L X h

variable [Finite G]

theorem component_arbitrary_action (L X : Subgroup G)
    (hL : IsComponentOf L ⊤) : L ≤ ⁅L, X⁆ ∨ ⁅L, X⁆ = ⊥ := by
  let A := L ⊔ X
  let N := ⁅L, X⁆
  have hNA : N ≤ A := Subgroup.commutator_le_sup L X
  let : (N.subgroupOf A).Normal := inferInstance
  have hlocal := LocalComponents.normal_contains_or_commutes
    (L.subgroupOf A) (N.subgroupOf A) (LocalComponents.of_overgroup hL le_sup_left)
  rcases hlocal with hcontained | hcommutes
  · left
    intro l hl
    exact hcontained (show (⟨l, (le_sup_left : L ≤ A) hl⟩ : A) ∈ L.subgroupOf A from hl)
  · right
    have hmap := congrArg (Subgroup.map A.subtype) hcommutes
    have hdouble : ⁅L, N⁆ = ⊥ := by
      have hmapL : (L.subgroupOf A).map A.subtype = L :=
        Subgroup.map_subgroupOf_eq_of_le (le_sup_left : L ≤ A)
      have hmapN : (N.subgroupOf A).map A.subtype = N :=
        Subgroup.map_subgroupOf_eq_of_le hNA
      rw [Subgroup.map_commutator, hmapL, hmapN, Subgroup.map_bot] at hmap
      exact hmap
    let : Group.IsPerfect L := ⟨hL.2.2.1⟩
    exact Quasisimple.perfect_double_commutator L X
      (by rwa [Subgroup.commutator_comm N L])


theorem layer_full_central_product :
    Layer.subgroup G = sSup {L : Subgroup G | IsComponentOf L ⊤} ∧
    (∀ L M : Subgroup G, IsComponentOf L ⊤ → IsComponentOf M ⊤ →
      L ≠ M → ⁅L, M⁆ = ⊥) ∧
    Function.Surjective (LayerMultiplication.multiplication G) ∧
    (LayerMultiplication.multiplication G).ker ≤
      Subgroup.center ((L : SemisimpleComponentStructure.ComponentIndex G) → L.val) ∧
    (∀ L : Subgroup G, IsComponentOf L ⊤ → (L.subgroupOf (Layer.subgroup G)).Normal) := by
  exact ⟨rfl, fun L M hL hM hne => LocalComponents.commute_of_ne L M hL hM hne,
    LayerMultiplication.surjective G, LayerMultiplication.kernel_le_center G,
    fun _ hL => Layer.normal_component hL⟩


end CFSG.ComponentClassification.AschbacherComponentAction
