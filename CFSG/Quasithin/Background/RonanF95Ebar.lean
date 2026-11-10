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

public section

namespace CFSG.Quasithin.RonanF95

open scoped Pointwise

variable {G : Type*} [Group G]

structure FormHyp (V₁ P : Subgroup G) : Prop where
  card : Nat.card V₁ = 2
  le : V₁ ≤ P
  central : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p
  sq : ∀ p ∈ P, p * p ∈ V₁
  comm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁

variable {V₁ P : Subgroup G}


abbrev Ebar (V₁ P : Subgroup G) [(V₁.subgroupOf P).Normal] : Type _ := ↥P ⧸ V₁.subgroupOf P

namespace FormHyp

variable [(V₁.subgroupOf P).Normal]

@[expose, instance_reducible] noncomputable def commGroup (_hP : FormHyp V₁ P) : CommGroup (Ebar V₁ P) :=
  { (inferInstance : Group (Ebar V₁ P)) with
    mul_comm := fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      have key : ((a : G) * b)⁻¹ * ((b : G) * a) =
          (b : G)⁻¹ * (a : G)⁻¹ * ((b : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by group
      rw [key]
      exact _hP.comm _ (P.inv_mem b.2) _ (P.inv_mem a.2) }


end FormHyp

end CFSG.Quasithin.RonanF95
