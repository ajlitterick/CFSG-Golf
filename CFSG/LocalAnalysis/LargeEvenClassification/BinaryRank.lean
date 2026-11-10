module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped MatrixGroups

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem card_linear_aut_binary (Space : Type groupUniverse) [AddCommGroup Space]
    [Module (ZMod 2) Space] [Finite Space] :
    Nat.card (Space ≃ₗ[ZMod 2] Space) =
      Nat.card (GL (Fin (Module.finrank (ZMod 2) Space)) (ZMod 2)) := by
  classical
  let basis := Module.finBasis (ZMod 2) Space
  let equivalence := (Matrix.GeneralLinearGroup.toLin' basis).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space)
  exact (Nat.card_congr equivalence.toEquiv).symm

theorem card_dvd_of_injective_hom {Source : Type groupUniverse} [Group Source]
    {Target : Type groupUniverse} [Group Target] (embedding : Source →* Target)
    (hinjective : Function.Injective embedding) : Nat.card Source ∣ Nat.card Target := by
  have hequivalence : Source ≃* embedding.range :=
    MonoidHom.ofInjective hinjective
  rw [Nat.card_congr hequivalence.toEquiv]
  exact embedding.range.card_subgroup_dvd_card


end CFSG.LargeEvenClassification.Helpers
