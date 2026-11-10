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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.Quasithin.RonanF95

open Module

structure TwoInv (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] where
  b : E →ₗ[ZMod 2] E →ₗ[ZMod 2] ZMod 2
  q : E → ZMod 2
  v : Module.End (ZMod 2) E
  i : Module.End (ZMod 2) E
  X : Submodule (ZMod 2) E
  Y : Submodule (ZMod 2) E
  hq : ∀ x y, q (x + y) = q x + q y + b x y
  hbalt : ∀ x, b x x = 0
  hbnd : ∀ x, (∀ y, b x y = 0) → x = 0
  hv : v * v = 1
  hi : i * i = 1
  hqv : ∀ x, q (v x) = q x
  hqi : ∀ x, q (i x) = q x
  hXv : ∀ x, x ∈ X ↔ v x = x
  hYi : ∀ y, y ∈ Y ↔ i y = y
  hvX : ∀ y, v y + y ∈ X
  hiY : ∀ x, i x + x ∈ Y
  hXY : IsCompl X Y
  hqX : ∀ x ∈ X, q x = 0
  hqY : ∀ y ∈ Y, q y = 0

namespace TwoInv

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (S : TwoInv E)

@[expose] def t : Module.End (ZMod 2) E := S.v * S.i

@[expose] def D : Module.End (ZMod 2) E := S.v * S.i + S.i * S.v


end TwoInv

end CFSG.Quasithin.RonanF95
