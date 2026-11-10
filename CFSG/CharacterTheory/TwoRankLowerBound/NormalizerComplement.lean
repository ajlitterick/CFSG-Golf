module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicOddComplement
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem cyclic_two_group_automorphisms_isPGroup (G : Type*) [Group G] [Finite G]
    [IsCyclic G] (htwo : IsPGroup 2 G) : IsPGroup 2 (MulAut G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hcard⟩ := htwo.exists_card_eq
  apply IsPGroup.iff_card.mpr
  rw [IsCyclic.card_mulAut, hcard]
  cases exponent with
  | zero => exact ⟨0, by simp⟩
  | succ exponent =>
    exact ⟨exponent, by rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp⟩


end CFSG.TwoRankLowerBound.Helpers
