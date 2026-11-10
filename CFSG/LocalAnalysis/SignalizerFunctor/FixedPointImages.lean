module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageIndices

public section

universe actorUniverse groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction ActorType ImageType]

theorem equivariant_subgroup_image_invariant
    (homomorphism : GroupType →* ImageType)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) :
    ∀ actorElement : ActorType, ∀ element ∈ subgroup.map homomorphism,
      actorElement • element ∈ subgroup.map homomorphism := by
  rintro actorElement element ⟨original, member, rfl⟩
  rw [← equivariant]
  exact Subgroup.mem_map_of_mem homomorphism (invariant actorElement original member)


theorem fixed_normalized_subgroup_image (prime : ℕ) (prime_prime : prime.Prime)
    (actor_pgroup : IsPGroup prime ActorType)
    (homomorphism : GroupType →* ImageType) (surjective : Function.Surjective homomorphism)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (kernel_coprime : Nat.Coprime prime (Nat.card homomorphism.ker))
    (subgroup : Subgroup GroupType)
    (normalized : FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (subgroup : Set GroupType)) :
    FixedPoints.subgroup ActorType ImageType ≤
      Subgroup.normalizer (subgroup.map homomorphism : Set ImageType) := by
  rw [← fixed_subgroup_map prime prime_prime actor_pgroup homomorphism surjective equivariant kernel_coprime]
  exact (Subgroup.map_mono normalized).trans (Subgroup.le_normalizer_map homomorphism)

end CFSG.SignalizerFunctor.Helpers
