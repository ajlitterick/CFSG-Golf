module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.ConjugationPairStabilizer
public import CFSG.LocalAnalysis.ComponentClassification.OrbitImageTransport

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.ComponentClassification.BlockPermutationAction

@[expose, instance_reducible] noncomputable def action {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component) :
    MulAction (UniversalOrbitBlock.normalizer component) ↥(UniversalOrbitBlock.block component) where
  smul actor factor := ⟨UniversalOrbitBlock.conjugate factor.val actor.val,
    (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor.val).mp
      actor.property factor.val factor.property⟩
  one_smul factor := Subtype.ext (UniversalOrbitBlock.conjugate_one factor.val)
  mul_smul first second factor := Subtype.ext (UniversalOrbitBlock.conjugate_conjugate factor.val second.val first.val).symm

@[expose] noncomputable def permutation {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Fin 3 ≃ ↥(UniversalOrbitBlock.block component)) :
    UniversalOrbitBlock.normalizer component →* Equiv.Perm (Fin 3) :=
  let := action component heven huniversal hquasisimple
  label.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (UniversalOrbitBlock.normalizer component)
    ↥(UniversalOrbitBlock.block component))


end CFSG.ComponentClassification.BlockPermutationAction
