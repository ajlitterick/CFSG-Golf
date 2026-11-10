module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSpectrum
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorRestriction

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]


omit [Finite GroupType] in
theorem signalizer_compatible_congr_values (prime rank : ℕ) (actor : Subgroup GroupType)
    (first second : Subgroup GroupType → Subgroup GroupType)
    (equal : ∀ selected ∈ signalizerFunctorEk prime rank actor, first selected = second selected)
    (target : Subgroup GroupType) :
    signalizerCompatible prime rank actor first target ↔
      signalizerCompatible prime rank actor second target := by
  constructor
  · intro compatible
    refine ⟨compatible.1, ?_⟩
    intro selected member
    rw [← equal selected member]
    exact compatible.2 selected member
  · intro compatible
    refine ⟨compatible.1, ?_⟩
    intro selected member
    rw [equal selected member]
    exact compatible.2 selected member

omit [Finite GroupType] in
theorem signalizer_completion_congr_values (prime rank : ℕ) (actor : Subgroup GroupType)
    (first second : Subgroup GroupType → Subgroup GroupType)
    (equal : ∀ selected ∈ signalizerFunctorEk prime rank actor, first selected = second selected) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor, first selected) =
      ⨆ selected ∈ signalizerFunctorEk prime rank actor, second selected := by
  congr 1
  funext selected
  congr 1
  funext member
  exact equal selected member

omit [Finite GroupType] in
theorem signalizer_restriction_complete_of_compatible (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (normalized : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (complete : signalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected)) :
    signalizerCompatible prime rank actor (signalizerRestriction values ambient)
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, signalizerRestriction values ambient selected) := by
  have completion_le : (⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient selected) ≤
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓ ambient := by
    apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact le_inf (inf_le_left.trans (signalizer_value_le_completion prime rank actor values member))
      inf_le_right
  refine ⟨signalizer_completion_normalized prime rank actor (signalizerRestriction values ambient)
    (fun selected member => normalizer_inf_of_le actor _ _ (normalized selected member)
      ambient_normalized), ?_⟩
  intro selected member
  exact le_inf ((inf_le_inf_right _ (completion_le.trans inf_le_left)).trans
    (complete.2 selected member)) (inf_le_left.trans (completion_le.trans inf_le_right))

omit [Finite GroupType] in
theorem signalizer_prime_value_eq_of_prime_support_agrees (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (first second : Set ℕ) (selected : Subgroup GroupType)
    (agrees : ∀ candidate ≤ values selected,
      primeSupported first (Nat.card candidate) ↔ primeSupported second (Nat.card candidate)) :
    signalizerPrimeValue prime rank actor values first selected =
      signalizerPrimeValue prime rank actor values second selected := by
  apply le_antisymm
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro property
    exact signalizer_prime_value_contains prime rank actor values second selected candidate property.1
      ((agrees candidate property.1).mp property.2.1) property.2.2.1 property.2.2.2
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro property
    exact signalizer_prime_value_contains prime rank actor values first selected candidate property.1
      ((agrees candidate property.1).mpr property.2.1) property.2.2.1 property.2.2.2


end CFSG.SignalizerFunctor.Helpers
