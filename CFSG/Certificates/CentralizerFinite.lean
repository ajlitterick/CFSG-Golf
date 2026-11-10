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
public import Mathlib.GroupTheory.Schreier
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

namespace CFSG.Certificates

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_center_left {z : G} (hz : z ∈ center G) (g h : G) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hzh : z * h = h * z := (mem_center_iff.mp hz h).symm
  rw [commutatorElement_def, commutatorElement_def, mul_assoc g z h, hzh]
  group

theorem commutatorElement_mul_center_right {z : G} (hz : z ∈ center G) (g h : G) :
    ⁅g, h * z⁆ = ⁅g, h⁆ := by
  have hzg : z * g = g * z := (mem_center_iff.mp hz g).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have : g * (h * z) * g⁻¹ * (z⁻¹ * h⁻¹) = g * h * (z * g⁻¹) * z⁻¹ * h⁻¹ := by group
  have hz' : z * g⁻¹ = g⁻¹ * z := by
    have := (mem_center_iff.mp hz g⁻¹).symm
    exact this
  rw [this, hz']
  group

theorem finite_commutatorSet_of_finiteIndex_center [(center G).FiniteIndex] :
    Finite (commutatorSet G) := by
  have : Finite (G ⧸ center G) := Subgroup.finite_quotient_of_finiteIndex
  refine Set.Finite.to_subtype (Set.Finite.subset
    (Set.finite_range (fun p : (G ⧸ center G) × (G ⧸ center G) => ⁅p.1.out, p.2.out⁆)) ?_)
  rintro _ ⟨g, h, rfl⟩
  refine ⟨((g : G ⧸ center G), (h : G ⧸ center G)), ?_⟩
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (center G) g
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (center G) h
  simp only
  rw [hz, hw, commutatorElement_mul_center_left z.2, commutatorElement_mul_center_right w.2]


end CFSG.Certificates
