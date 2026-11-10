module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

@[expose] def fusedSet (u t : G) : Set G :=
  {t' | IsConj t t' ∧ t' * u = u * t' ∧ t' * t = t * t'}

@[expose] def Sol78Fusion (u t : G) : Prop := ∀ t' ∈ fusedSet u t, t' = t ∨ t' = u * t


omit [Finite G] in
theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

omit [Finite G] in
theorem ne_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  exact absurd hx (by decide)

omit [Finite G] in
theorem zpow_eq_one_or_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  rw [← zpow_mod_orderOf, hx]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h0 | h1
  · left
    rw [h0]
    simp
  · right
    rw [h1]
    simp


end CFSG.EvenSporadicStandard.Solomon78
