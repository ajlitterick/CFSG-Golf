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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module Equiv Equiv.Perm

@[expose] def sumForm (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[expose] def evenWeight (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (sumForm n)

theorem mem_evenWeight {n : ℕ} {x : Fin n → ZMod 2} : x ∈ evenWeight n ↔ ∑ i, x i = 0 :=
  Iff.rfl


theorem funLeft_inv_apply {n : ℕ} (g : Perm (Fin n)) (x : Fin n → ZMod 2) (i : Fin n) :
    LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ x i = x (g⁻¹ i) :=
  rfl

theorem funLeft_inv_mem_evenWeight {n : ℕ} (g : Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ evenWeight n) : LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ x ∈ evenWeight n := by
  rw [mem_evenWeight] at hx ⊢
  simp only [funLeft_inv_apply]
  rw [Equiv.sum_comp g⁻¹ x, hx]


end CFSG.Quasithin.SteinbergCB
