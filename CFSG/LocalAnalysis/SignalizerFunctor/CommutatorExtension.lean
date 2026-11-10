module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.PGroupFamilyNormalizer

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem commutator_extension_normalized (actor parent target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType)) (target_le : target ≤ parent) :
    actor ≤ Subgroup.normalizer ((target ⊔ ⁅parent, actor⁆ : Subgroup GroupType) : Set GroupType) := by
  let commutators : Subgroup GroupType := ⁅parent, actor⁆
  let combined := target ⊔ commutators
  have commutators_normalized := normalized_commutator_normalized actor parent normalized
  apply Subgroup.le_normalizer_iff.mpr
  intro actorElement actor_member element member
  have image_le : combined.map (MulAut.conj actorElement).toMonoidHom ≤ combined := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨original, original_member, rfl⟩
      change actorElement * original * actorElement⁻¹ ∈ combined
      have generated := Subgroup.commutator_mem_commutator (parent.inv_mem (target_le original_member)) actor_member
      have difference_member : original⁻¹ * (actorElement * original * actorElement⁻¹) ∈ commutators := by
        simpa only [commutatorElement_def, inv_inv, mul_assoc] using generated
      have product := combined.mul_mem (Subgroup.mem_sup_left original_member) (Subgroup.mem_sup_right difference_member)
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using product
    · exact (normalized_conjugate_subgroup_le actor commutators commutators_normalized actorElement actor_member).trans
        le_sup_right
  exact image_le (Subgroup.mem_map_of_mem _ member)


end CFSG.SignalizerFunctor.Helpers
