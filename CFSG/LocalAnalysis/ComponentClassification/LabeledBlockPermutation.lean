module

public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockSupport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LabeledBlockPermutation

@[expose] noncomputable def permutation {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component)) :
    UniversalOrbitBlock.normalizer component →* Equiv.Perm Index :=
  let := BlockPermutationAction.action component heven huniversal hquasisimple
  label.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (UniversalOrbitBlock.normalizer component) ↥(UniversalOrbitBlock.block component))


@[expose] noncomputable def image {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component)) (factor : Subgroup G) : Subgroup (Equiv.Perm Index) :=
  (factor.subgroupOf (UniversalOrbitBlock.normalizer component)).map
    (permutation component heven huniversal hquasisimple label)


end CFSG.ComponentClassification.LabeledBlockPermutation
