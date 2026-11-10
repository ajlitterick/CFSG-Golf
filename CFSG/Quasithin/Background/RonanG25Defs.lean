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
public import Mathlib.RingTheory.Henselian
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
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.RonanG25

section Defs

variable {G : Type} [Group G]


@[expose] def FactorCentral (X A B : Subgroup G) : Prop :=
  ∀ x ∈ X, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ A

@[expose] def FactorNatural (F : Type) [Field F] (X A B : Subgroup G) : Prop :=
  ∃ (φ : ↥B →* Multiplicative (Fin 2 → F)) (β : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F),
    Function.Surjective φ ∧ (∀ y : ↥B, φ y = 1 ↔ (y : G) ∈ A) ∧
    (∀ (x : ↥X) (y y' : ↥B), (x : G) * (y : G) * (x : G)⁻¹ = (y' : G) →
      Multiplicative.toAdd (φ y') =
        ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (φ y))) ∧
    (Nat.card F = 2 → β ≠ 1) ∧
    (2 < Nat.card F → ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F))


@[expose] def FactorTwo (A B : Subgroup G) : Prop :=
  ∃ dimension : ℕ, 0 < dimension ∧ Nat.card ↥B = 2 ^ dimension * Nat.card ↥A


end Defs

section Chain

variable {G : Type} [Group G]

@[expose] def Inv (X A : Subgroup G) : Prop := ∀ x ∈ X, ∀ y ∈ A, x * y * x⁻¹ ∈ A

structure ChiefStep (X A B : Subgroup G) : Prop where
  lt : A < B
  invA : Inv X A
  invB : Inv X B
  normal : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A
  simple : ∀ Q : Subgroup G, A ≤ Q → Q ≤ B → Inv X Q → (∀ y ∈ B, ∀ z ∈ Q, y * z * y⁻¹ ∈ Q) →
    Q = A ∨ Q = B

inductive ChainCounts (F : Type) [Field F] (X : Subgroup G) (ord : Bool) :
    Subgroup G → Subgroup G → ℕ → ℕ → Prop
  | refl (A : Subgroup G) (hA : Inv X A) : ChainCounts F X ord A A 0 0
  | natural {A B C : Subgroup G} {a b : ℕ} (hs : ChiefStep X A B) (hn : FactorNatural F X A B)
      (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C (a + 1) b
  | additional {A B C : Subgroup G} {a b : ℕ} (hs : ChiefStep X A B)
      (habel : ∀ y ∈ B, ∀ z ∈ B, y * z * y⁻¹ * z⁻¹ ∈ A)
      (hc : ¬ FactorCentral X A B) (hcard : Nat.card B = Nat.card F * Nat.card A)
      (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C a (b + 1)
  | central {A B C : Subgroup G} {a b : ℕ} (hs : ChiefStep X A B) (hc : FactorCentral X A B)
      {p : ℕ} (hp : p.Prime) (hcard : Nat.card B = p * Nat.card A)
      (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C a b
  | other {A B C : Subgroup G} {a b : ℕ} (hord : ord = true) (hs : ChiefStep X A B)
      (h2 : ¬ FactorTwo A B) (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C a b


end Chain

end CFSG.Quasithin.RonanG25
