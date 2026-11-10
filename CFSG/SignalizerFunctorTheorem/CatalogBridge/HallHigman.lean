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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Module Module.End Polynomial

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem iSup_iInf_eigenspace_eq_top_of_commute {K V ι : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : ι → Module.End K V)
    (hss : ∀ i, (f i).IsSemisimple) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
  have h1 : ∀ i μ, (f i).maxGenEigenspace μ = (f i).eigenspace μ := fun i μ =>
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcomm i j) (fun i => by
      simp only [h1]; exact (hss i).iSup_eigenspace_eq_top)
  simpa only [h1] using this


theorem pow_eq_one_of_sub_one_pow_eq_zero {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {a : A} (h : (a - 1) ^ (ℓ - 1) = 0) : a ^ ℓ = 1 := by
  have h1 : (a - 1) ^ ℓ = a ^ ℓ - 1 := by
    have := congrArg (aeval a) (sub_pow_char (X : K[X]) 1)
    simpa using this
  have h2 : (a - 1) ^ ℓ = 0 := by
    rw [← Nat.sub_add_cancel (Fact.out : ℓ.Prime).one_le, pow_succ, h, zero_mul]
  rw [h1] at h2
  exact sub_eq_zero.mp h2


end CFSG.SignalizerFunctorTheorem.CatalogBridge
