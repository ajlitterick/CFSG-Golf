module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductJointLocalSylow
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductSurvivingKernel
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductLocalCommutatorNontrivial

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_kernel_intersection (fixedActor kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor)
    (fixedActor_large : prime ^ (rank + 1) ≤ Nat.card fixedActor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}))
    (localFactor_nontrivial : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≠ ⊥)
    (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime)
    (kernelPrime_spectrum : kernelPrime ∈ signalizerSpectrum prime rank actor values)
    (kernelPrime_distinct : kernelPrime ≠ groupPrime) (kernel_coprime : Nat.Coprime kernelPrime (Nat.card kernel)) :
    kernel ≤ conjugateIntersection (factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)) complement := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let localCore := (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  have fixedActor_elementary := elementary_abelian_of_le prime datum.elementary fixedActor_le
  have selected_rank : prime ^ rank ≤ Nat.card fixedActor := by
    apply le_trans _ fixedActor_large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ datum.prime_prime.pos
  obtain ⟨selected, selected_member⟩ := signalizerFunctorEk_nonempty prime rank datum.prime_prime fixedActor
    fixedActor_elementary selected_rank
  have selected_global : selected ∈ signalizerFunctorEk prime rank actor :=
    ⟨selected_member.1.trans fixedActor_le, selected_member.2⟩
  obtain ⟨sylow, normalized, factor_normalized⟩ := incomplete_hall_product_joint_local_core_sylow fixedActor selected
    datum fixedActor_le selected_global selected_member.1 kernelPrime kernelPrime_prime
  let witness := (sylow : Subgroup localCore).map localCore.subtype
  have witness_nontrivial := incomplete_abelian_hall_product_local_commutator_nontrivial fixedActor selected kernel datum
    abelian fixedActor_le selected_global selected_member.1 common_le_parent localFactor_nontrivial kernel_le
    kernel_nontrivial kernel_normal kernel_normalized common_normalized kernelPrime kernelPrime_prime kernelPrime_spectrum
    kernelPrime_distinct kernel_coprime sylow normalized
  have witness_pgroup : IsPGroup kernelPrime witness := sylow.isPGroup'.map localCore.subtype
  exact incomplete_abelian_hall_product_surviving_kernel_le_intersection fixedActor witness kernel datum abelian
    fixedActor_le fixedActor_large common_le_parent complement_eq kernelPrime kernelPrime_prime witness_pgroup
    (Subgroup.map_subtype_le _) normalized factor_normalized localFactor_nontrivial witness_nontrivial
    kernel_le kernel_normal kernel_normalized kernel_coprime


end CFSG.SignalizerFunctor.Helpers
