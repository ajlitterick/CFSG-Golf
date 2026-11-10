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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.ShultG53

open Equiv

@[expose] def mkP (v w : Fin 6 → Fin 6) (h₁ : ∀ i, w (v i) = i := by decide)
    (h₂ : ∀ i, v (w i) = i := by decide) : Perm (Fin 6) := ⟨v, w, h₁, h₂⟩


@[expose] def T5_0 : Fin 2 → Perm (Fin 6) := ![
  mkP ![0,2,1,3,5,4] ![0,2,1,3,5,4],
  mkP ![0,3,1,2,4,5] ![0,2,3,1,4,5]]

@[expose] def T5_1 : Fin 2 → Perm (Fin 6) := ![
  mkP ![0,1,4,5,2,3] ![0,1,4,5,2,3],
  mkP ![2,3,4,5,0,1] ![4,5,0,1,2,3]]

end CFSG.Quasithin.ShultG53
