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

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise

variable {A : Type*} [Group A] {B : Type*} [Group B]

theorem commutator_mul_central_left {a z b : A} (hzb : z * b = b * z) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b * z⁻¹ = b := by rw [hzb]; group
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem commutator_mul_central_right {a b w : A} (hwa : w * a = a * w) :
    ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have h : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    have : Commute w a := hwa
    have h2 : w * a⁻¹ = a⁻¹ * w := this.inv_right.eq
    rw [h2]; group
  simp only [commutatorElement_def]
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]


end CFSG.Quasithin
