module

public import CFSG.LocalAnalysis.SignalizerFunctor.SylowNormalizerPromotion
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure

public section

universe groupUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]


theorem solvable_matsuyama_complement_core [Finite GroupType] [Group.IsSolvable GroupType]
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (distinct : groupPrime ≠ prime) (sylow : Sylow prime GroupType) (target : Subgroup GroupType)
    (orbit_pgroup : ∀ element : GroupType,
      IsPGroup groupPrime (normalizedConjugateHull (sylow : Subgroup GroupType) (conjugateSubgroup element target))) :
    target ≤ primeSetCore ({prime}ᶜ) := by
  obtain ⟨targetSylow, target_le, normalized⟩ := matsuyama_weak_closure groupPrime groupPrime_prime
    (sylow : Subgroup GroupType) target orbit_pgroup
  have weak_pgroup : IsPGroup groupPrime (subgroupWeakClosure target targetSylow) :=
    targetSylow.isPGroup'.to_le (subgroup_weak_closure_le target targetSylow)
  have weak_coprime : Nat.Coprime prime (Nat.card (subgroupWeakClosure target targetSylow)) :=
    prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct.symm weak_pgroup
  exact (subgroup_le_weak_closure target targetSylow target_le).trans
    (solvable_sylow_normalized_complement_le_core prime prime_prime sylow _ weak_coprime normalized)

end CFSG.SignalizerFunctor.Helpers
