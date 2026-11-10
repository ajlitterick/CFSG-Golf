module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

section

variable {source target : Type*} [Ring source] [CommRing target] [Module source target]
  (quotient : source →+* target)
  (hmodule : ∀ scalar : source, ∀ value : target, scalar • value = quotient scalar * value)

@[expose] noncomputable def quotientRegularMultiplication : target →+* Module.End source target where
  toFun coefficient :=
    { toFun := fun value => coefficient * value
      map_add' := fun left right => mul_add coefficient left right
      map_smul' := by
        intro scalar value
        simp only [hmodule, RingHom.id_apply]
        ring }
  map_one' := by
    apply LinearMap.ext
    intro value
    exact one_mul value
  map_mul' := by
    intro left right
    apply LinearMap.ext
    intro value
    exact mul_assoc left right value
  map_zero' := by
    apply LinearMap.ext
    intro value
    exact zero_mul value
  map_add' := by
    intro left right
    apply LinearMap.ext
    intro value
    exact add_mul left right value

theorem quotientRegularMultiplication_apply (coefficient value : target) :
    quotientRegularMultiplication quotient hmodule coefficient value = coefficient * value := rfl


theorem quotientRegular_endomorphism_eq (hsurjective : Function.Surjective quotient)
    (operator : Module.End source target) :
    quotientRegularMultiplication quotient hmodule (operator 1) = operator := by
  apply LinearMap.ext
  intro value
  obtain ⟨scalar, hscalar⟩ := hsurjective value
  have hequal := operator.map_smul scalar (1 : target)
  simp only [hmodule] at hequal
  simpa only [quotientRegularMultiplication_apply, mul_one, hscalar, mul_comm] using hequal.symm


include hmodule in
theorem quotientRegular_endomorphism_unit_or_complement (hsurjective : Function.Surjective quotient)
    (hlocal : ∀ coefficient : target, IsUnit coefficient ∨ IsUnit (1 - coefficient))
    (operator : Module.End source target) :
    IsUnit operator ∨ IsUnit (1 - operator) := by
  have hequal := quotientRegular_endomorphism_eq quotient hmodule hsurjective operator
  rcases hlocal (operator 1) with hunit | hunit
  · left
    exact hequal ▸ hunit.map (quotientRegularMultiplication quotient hmodule)
  · right
    have hmapped := hunit.map (quotientRegularMultiplication quotient hmodule)
    rwa [map_sub, map_one, hequal] at hmapped

end

end CFSG.TwoRankLowerBound.Helpers
