module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleProductCentralizers

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem normal_core_map_automorphism (subgroup : Subgroup GroupType) (equivalence : GroupType ≃* GroupType) :
    subgroup.normalCore.map equivalence.toMonoidHom = (subgroup.map equivalence.toMonoidHom).normalCore := by
  have map_le : ∀ candidate : Subgroup GroupType, ∀ isomorphism : GroupType ≃* GroupType,
      candidate.normalCore.map isomorphism.toMonoidHom ≤ (candidate.map isomorphism.toMonoidHom).normalCore := by
    intro candidate isomorphism
    let _normal := (inferInstance : candidate.normalCore.Normal).map isomorphism.toMonoidHom isomorphism.surjective
    exact Subgroup.normal_le_normalCore.mpr (Subgroup.map_mono candidate.normalCore_le)
  apply le_antisymm (map_le subgroup equivalence)
  have inverse_le := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (map_le (subgroup.map equivalence.toMonoidHom) equivalence.symm)
  have identity_first : equivalence.symm.toMonoidHom.comp equivalence.toMonoidHom = MonoidHom.id GroupType := by
    ext element
    exact equivalence.symm_apply_apply element
  have identity_second : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom = MonoidHom.id GroupType := by
    ext element
    exact equivalence.apply_symm_apply element
  simp only [Subgroup.map_map, identity_first, Subgroup.map_id, identity_second,
    Subgroup.map_id] at inverse_le
  exact inverse_le


end CFSG.SignalizerFunctor.Helpers
