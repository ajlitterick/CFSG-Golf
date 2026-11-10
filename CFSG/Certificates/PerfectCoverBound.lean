module

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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

theorem perfect_hom_comm_trivial {G A : Type*} [Group G] [Group A] [IsMulCommutative A]
    [Group.IsPerfect G] (f : G →* A) (g : G) : f g = 1 := by
  have := Abelianization.commutator_subset_ker f
  have hg : g ∈ commutator G := by simp
  exact this hg

theorem perfect_perm_trivial {G α : Type*} [Group G] [Group.IsPerfect G] [Finite α]
    (hα : Nat.card α ≤ 4) (κ : G →* Equiv.Perm α) (g : G) : κ g = 1 := by
  classical
  have := Fintype.ofFinite α
  have hsign : ∀ x, Equiv.Perm.sign (κ x) = 1 := fun x =>
    perfect_hom_comm_trivial (Equiv.Perm.sign.comp κ) x
  have hmem : ∀ x, κ x ∈ alternatingGroup α := fun x => by
    rw [alternatingGroup, MonoidHom.mem_ker]; exact hsign x
  let κ' : G →* alternatingGroup α := κ.codRestrict _ hmem
  have hsolv : Group.IsSolvable (alternatingGroup α) := alternatingGroup.isSolvable hα
  have hp : Group.IsPerfect κ'.range := Group.IsPerfect.range κ'
  have hs : Group.IsSolvable κ'.range := inferInstance
  by_contra hne
  have hne' : κ' g ≠ 1 := by
    intro h
    apply hne
    have := congrArg Subtype.val h
    simpa [κ'] using this
  have hnt : Nontrivial κ'.range :=
    ⟨⟨⟨κ' g, g, rfl⟩, 1, fun h => hne' (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable κ'.range hs

theorem normal_le_center_of_card_le_four {E : Type*} [Group E] [Group.IsPerfect E]
    (Q : Subgroup E) [Q.Normal] [Finite Q] (hQ : Nat.card Q ≤ 4) : Q ≤ Subgroup.center E := by
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  have h := perfect_perm_trivial (G := E) (α := Q) hQ ((MulAut.toPerm Q).comp MulAut.conjNormal) g
  have h2 := congrArg (fun p : Equiv.Perm Q => ((p ⟨q, hq⟩ : Q) : E)) h
  have h3 : g * q * g⁻¹ = q := by
    have : (((MulAut.toPerm Q).comp MulAut.conjNormal) g) ⟨q, hq⟩ =
        (MulAut.conjNormal g : MulAut Q) ⟨q, hq⟩ := rfl
    simp only [this, MulAut.conjNormal_apply] at h2
    simpa using h2
  calc g * q = g * q * g⁻¹ * g := by group
    _ = q * g := by rw [h3]


end CFSG.Certificates
