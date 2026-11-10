module

public import CFSG.LocalAnalysis.SignalizerFunctor.SylowGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def fittingSubgroup : Subgroup GroupType :=
  ⨆ (candidate : Subgroup GroupType) (_ : candidate.Normal ∧ Group.IsNilpotent candidate), candidate

theorem fitting_subgroup_contains (candidate : Subgroup GroupType)
    (normal : candidate.Normal) (nilpotent : Group.IsNilpotent candidate) :
    candidate ≤ fittingSubgroup :=
  le_iSup_of_le candidate (le_iSup_of_le ⟨normal, nilpotent⟩ le_rfl)

theorem fitting_subgroup_normal : (fittingSubgroup (GroupType := GroupType)).Normal := by
  let candidates := {candidate : Subgroup GroupType // candidate.Normal ∧ Group.IsNilpotent candidate}
  let _normals : ∀ candidate : candidates, candidate.val.Normal := fun candidate => candidate.property.1
  have normal : (⨆ candidate : candidates, candidate.val).Normal := inferInstance
  have equal : (⨆ candidate : candidates, candidate.val) = fittingSubgroup := iSup_subtype
  rwa [equal] at normal

theorem fitting_subgroup_map_isomorphism {ImageType : Type imageUniverse} [Group ImageType]
    (equivalence : GroupType ≃* ImageType) :
    (fittingSubgroup (GroupType := GroupType)).map equivalence.toMonoidHom = fittingSubgroup := by
  have map_le : ∀ {Source : Type groupUniverse} [Group Source]
      {Target : Type imageUniverse} [Group Target] (isomorphism : Source ≃* Target),
      (fittingSubgroup (GroupType := Source)).map isomorphism.toMonoidHom ≤ fittingSubgroup := by
    intro Source _ Target _ isomorphism
    unfold fittingSubgroup
    simp only [Subgroup.map_iSup]
    apply iSup_le
    intro candidate
    apply iSup_le
    intro properties
    apply fitting_subgroup_contains
    · exact properties.1.map isomorphism.toMonoidHom isomorphism.surjective
    · let := properties.2
      exact Group.nilpotent_of_mulEquiv (candidate.equivMapOfInjective isomorphism.toMonoidHom
        isomorphism.injective)
  apply le_antisymm (map_le equivalence)
  have inverse_le : (fittingSubgroup (GroupType := ImageType)).map equivalence.symm.toMonoidHom ≤
      fittingSubgroup := by
    unfold fittingSubgroup
    simp only [Subgroup.map_iSup]
    apply iSup_le
    intro candidate
    apply iSup_le
    intro properties
    apply fitting_subgroup_contains
    · exact properties.1.map equivalence.symm.toMonoidHom equivalence.symm.surjective
    · let := properties.2
      exact Group.nilpotent_of_mulEquiv (candidate.equivMapOfInjective equivalence.symm.toMonoidHom
        equivalence.symm.injective)
  have mapped_le := Subgroup.map_mono (f := equivalence.toMonoidHom) inverse_le
  rw [Subgroup.map_map] at mapped_le
  have identity : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom = MonoidHom.id ImageType := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [identity, Subgroup.map_id] at mapped_le

theorem fitting_subgroup_characteristic : (fittingSubgroup (GroupType := GroupType)).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fitting_subgroup_map_isomorphism


theorem normal_nilpotent_le_prime_cores [Finite GroupType]
    (candidate : Subgroup GroupType) [candidate.Normal] [Group.IsNilpotent candidate] :
    candidate ≤ ⨆ prime : {prime : ℕ // prime.Prime}, primeSetCore {prime.val} := by
  let combined : Subgroup GroupType := ⨆ prime : {prime : ℕ // prime.Prime}, primeSetCore {prime.val}
  have contains : ∀ prime : ℕ, prime.Prime →
      ∃ sylow : Sylow prime candidate, (sylow : Subgroup candidate) ≤ combined.subgroupOf candidate := by
    intro prime prime_prime
    let : Fact prime.Prime := ⟨prime_prime⟩
    let sylow : Sylow prime candidate := Classical.choice inferInstance
    let _characteristic : (sylow : Subgroup candidate).Characteristic :=
      sylow.characteristic_of_normal inferInstance
    have embedded_normal := normal_of_characteristic_subgroup candidate (sylow : Subgroup candidate)
    have embedded_supported := (prime_supported_singleton_iff_pgroup prime prime_prime _).mpr
      (sylow.isPGroup'.map candidate.subtype)
    have embedded_le := (prime_set_core_contains {prime} _ embedded_normal embedded_supported).trans
      (le_iSup (fun prime : {prime : ℕ // prime.Prime} => primeSetCore {prime.val}) ⟨prime, prime_prime⟩)
    refine ⟨sylow, ?_⟩
    intro element member
    exact embedded_le (Subgroup.mem_map_of_mem candidate.subtype member)
  have equal := eq_top_of_sylow_containment (combined.subgroupOf candidate) contains
  intro element member
  have internal : (⟨element, member⟩ : candidate) ∈ combined.subgroupOf candidate := by
    rw [equal]
    trivial
  exact internal

theorem fitting_subgroup_eq_prime_cores [Finite GroupType] :
    fittingSubgroup (GroupType := GroupType) =
      ⨆ prime : {prime : ℕ // prime.Prime}, primeSetCore {prime.val} := by
  apply le_antisymm
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro properties
    let := properties.1
    let := properties.2
    exact normal_nilpotent_le_prime_cores candidate
  · apply iSup_le
    intro prime
    let : Fact prime.val.Prime := ⟨prime.property⟩
    exact fitting_subgroup_contains _ (prime_set_core_normal {prime.val})
      (prime_core_isPGroup prime.val prime.property).isNilpotent


end CFSG.SignalizerFunctor.Helpers
