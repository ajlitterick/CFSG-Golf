module

public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleComponentStructure
public import CFSG.LocalAnalysis.ComponentClassification.PerfectFiniteProduct

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.LayerMultiplication

local instance componentIndexFinite (G : Type*) [Group G] [Finite G] :
    Finite (SemisimpleComponentStructure.ComponentIndex G) := by
  unfold SemisimpleComponentStructure.ComponentIndex
  infer_instance

noncomputable instance componentIndexFintype (G : Type*) [Group G] [Finite G] :
    Fintype (SemisimpleComponentStructure.ComponentIndex G) := Fintype.ofFinite _

theorem coordinate_commute (G : Type*) [Group G] [Finite G] :
    Pairwise (fun first second : SemisimpleComponentStructure.ComponentIndex G =>
      ∀ left right : G, left ∈ first.val → right ∈ second.val → Commute left right) := by
  intro first second hne left right hleft hright
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne _ _ first.property second.property
        (fun heq => hne (Subtype.ext heq))) hleft) right hright).symm

@[expose] noncomputable def ambient (G : Type*) [Group G] [Finite G] :
    ((index : SemisimpleComponentStructure.ComponentIndex G) → index.val) →* G :=
  Subgroup.noncommPiCoprod (coordinate_commute G)

theorem range_eq_layer (G : Type*) [Group G] [Finite G] : (ambient G).range = Layer.subgroup G := by
  change (Subgroup.noncommPiCoprod (H := fun index : SemisimpleComponentStructure.ComponentIndex G => index.val)
    (coordinate_commute G)).range = Layer.subgroup G
  rw [Subgroup.noncommPiCoprod_range (H := fun index : SemisimpleComponentStructure.ComponentIndex G => index.val)]
  apply le_antisymm
  · apply iSup_le
    intro index
    exact Layer.component_le index.property
  · apply sSup_le
    intro component hcomponent
    exact le_iSup_of_le (⟨component, hcomponent⟩ : SemisimpleComponentStructure.ComponentIndex G) le_rfl

@[expose] noncomputable def multiplication (G : Type*) [Group G] [Finite G] :
    ((index : SemisimpleComponentStructure.ComponentIndex G) → index.val) →* Layer.subgroup G :=
  (ambient G).codRestrict (Layer.subgroup G) (fun member => range_eq_layer G ▸ ⟨member, rfl⟩)

theorem surjective (G : Type*) [Group G] [Finite G] : Function.Surjective (multiplication G) := by
  intro member
  have hmem : member.val ∈ (ambient G).range := (range_eq_layer G).symm ▸ member.property
  obtain ⟨lift, hlift⟩ := hmem
  exact ⟨lift, Subtype.ext hlift⟩

theorem kernel_coordinate_central {G : Type*} [Group G] [Finite G]
    (tuple : (index : SemisimpleComponentStructure.ComponentIndex G) → index.val)
    (hkernel : ambient G tuple = 1) (index : SemisimpleComponentStructure.ComponentIndex G) :
    tuple index ∈ Subgroup.center index.val := by
  classical
  let coordinate := fun index : SemisimpleComponentStructure.ComponentIndex G => ↥index.val
  apply Subgroup.mem_center_iff.mpr
  intro member
  have hcoordinateCommutator : ⁅tuple, Pi.mulSingle (M := coordinate) index member⁆ =
      Pi.mulSingle (M := coordinate) index ⁅tuple index, member⁆ := by
    funext other
    have hcommutatorApply : ⁅tuple, Pi.mulSingle (M := coordinate) index member⁆ other =
        ⁅tuple other, Pi.mulSingle (M := coordinate) index member other⁆ := by
      simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]
    rw [hcommutatorApply]
    by_cases heq : other = index
    · subst other
      simp only [Pi.mulSingle_eq_same]
    · simp only [Pi.mulSingle_eq_of_ne heq, commutatorElement_one_right]
  have hmap := map_commutatorElement (ambient G) tuple (Pi.mulSingle (M := coordinate) index member)
  rw [hkernel, commutatorElement_one_left, hcoordinateCommutator] at hmap
  have hcommutatorOne : (⁅tuple index, member⁆ : index.val).val = 1 := by
    have hvalue := Subgroup.noncommPiCoprod_mulSingle
      (H := fun index : SemisimpleComponentStructure.ComponentIndex G => index.val)
      (hcomm := coordinate_commute G) index
      ⁅tuple index, member⁆
    exact hvalue.symm.trans hmap
  have hlocalOne : ⁅tuple index, member⁆ = 1 := Subtype.ext hcommutatorOne
  exact (commutatorElement_eq_one_iff_mul_comm.mp hlocalOne).symm

theorem kernel_iff {G : Type*} [Group G] [Finite G]
    (tuple : (index : SemisimpleComponentStructure.ComponentIndex G) → index.val) :
    tuple ∈ (multiplication G).ker ↔
      (∀ index, tuple index ∈ Subgroup.center index.val) ∧ ambient G tuple = 1 := by
  constructor
  · intro hkernel
    have hone : ambient G tuple = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hkernel)
    exact ⟨kernel_coordinate_central tuple hone, hone⟩
  · rintro ⟨_, hone⟩
    exact MonoidHom.mem_ker.mpr (Subtype.ext hone)


theorem tuple_center_iff {G : Type*} [Group G] [Finite G]
    (tuple : (index : SemisimpleComponentStructure.ComponentIndex G) → index.val) :
    tuple ∈ Subgroup.center ((index : SemisimpleComponentStructure.ComponentIndex G) → index.val) ↔
      ∀ index, tuple index ∈ Subgroup.center index.val := by
  classical
  constructor
  · intro hcentral index
    apply Subgroup.mem_center_iff.mpr
    intro member
    have heq := congrArg (fun value : (index : SemisimpleComponentStructure.ComponentIndex G) → index.val =>
      value index) (Subgroup.mem_center_iff.mp hcentral
        (Pi.mulSingle (M := fun index : SemisimpleComponentStructure.ComponentIndex G => ↥index.val) index member))
    simpa only [Pi.mul_apply, Pi.mulSingle_eq_same] using heq
  · intro hcentral
    apply Subgroup.mem_center_iff.mpr
    intro other
    funext index
    exact Subgroup.mem_center_iff.mp (hcentral index) (other index)

theorem kernel_le_center (G : Type*) [Group G] [Finite G] :
    (multiplication G).ker ≤
      Subgroup.center ((index : SemisimpleComponentStructure.ComponentIndex G) → index.val) := by
  intro tuple hkernel
  exact (tuple_center_iff tuple).mpr ((kernel_iff tuple).mp hkernel).1


theorem component_center_intersection {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) :
    component ⊓ (Subgroup.center (Layer.subgroup G)).map (Layer.subgroup G).subtype =
      (Subgroup.center component).map component.subtype := by
  apply le_antisymm
  · intro member hmember
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmember.2
    have hcentral : (⟨member, hmember.1⟩ : component) ∈ Subgroup.center component := by
      apply Subgroup.mem_center_iff.mpr
      intro other
      have hotherLayer := Layer.component_le hcomponent other.property
      have hcommute := congrArg Subtype.val (Subgroup.mem_center_iff.mp hlift
        (⟨other.val, hotherLayer⟩ : Layer.subgroup G))
      change other.val * lift.val = lift.val * other.val at hcommute
      change lift.val = member at heq
      rw [heq] at hcommute
      exact Subtype.ext hcommute
    exact ⟨⟨member, hmember.1⟩, hcentral, rfl⟩
  · intro member hmember
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    refine ⟨lift.property, ?_⟩
    have hlayer := Layer.component_le hcomponent lift.property
    refine ⟨⟨lift.val, hlayer⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    have hcentralizes := ComponentAutomorphisms.center_le_layer_center component hcomponent
      (Subgroup.mem_map_of_mem component.subtype hlift)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcentralizes other.val other.property)

end CFSG.ComponentClassification.LayerMultiplication
