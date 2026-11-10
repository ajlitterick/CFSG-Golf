module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

instance zpowers_subgroupOf_inf_centralizer_normal (Q : Subgroup G) (a : G) :
    ((zpowers a).subgroupOf (Q ⊓ centralizer {a})).Normal where
  conj_mem x hx g := by
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hx
    have hga : Commute (g : G) a := mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).2
    have hgx : (g : G) * x * (g : G)⁻¹ = x := by
      rw [← hm, (hga.zpow_right m).eq, mul_inv_cancel_right]
    simpa only [coe_mul, coe_inv, hgx] using hx

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {a x : G} (ha : orderOf a = 2)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]


end CFSG.LocalAnalysis.GorensteinLyons
