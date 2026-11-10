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

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

noncomputable def conjOrb (N : Subgroup G) (x : G) : Finset G :=
  Finset.univ.filter fun y => ∃ n ∈ N, y = n * x * n⁻¹

theorem mem_conjOrb {N : Subgroup G} {x y : G} : y ∈ conjOrb N x ↔ ∃ n ∈ N, y = n * x * n⁻¹ := by
  simp [conjOrb]


theorem card_conjOrb_mul (N : Subgroup G) (x : G) :
    (conjOrb N x).card * Nat.card ↥(N ⊓ centralizer ({x} : Set G)) = Nat.card N := by
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : N) (y : G), n • y = (n : G) * y * (n : G)⁻¹ := fun n y => rfl
  have h1 := MulAction.index_stabilizer N x
  have h2 := (MulAction.stabilizer N x).card_mul_index
  have horb : (MulAction.orbit N x).ncard = (conjOrb N x).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp only [MulAction.mem_orbit_iff, Finset.mem_coe, mem_conjOrb, hsmul]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hstab : Nat.card (MulAction.stabilizer N x) = Nat.card ↥(N ⊓ centralizer ({x} : Set G)) := by
    have : MulAction.stabilizer N x = (centralizer ({x} : Set G)).subgroupOf N := by
      ext n
      simp only [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc (n : G) * x = ((n : G) * x * (n : G)⁻¹) * (n : G) := by group
          _ = x * (n : G) := by rw [h]
      · intro h
        calc (n : G) * x * (n : G)⁻¹ = (x * (n : G)) * (n : G)⁻¹ := by rw [h]
          _ = x := by group
    rw [this, ← Subgroup.inf_subgroupOf_right]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      centralizer ({x} : Set G) ⊓ N ≤ N)).toEquiv).trans ?_
    rw [inf_comm]
  rw [horb] at h1
  rw [hstab, h1] at h2
  rw [mul_comm]
  exact h2


end CFSG.EvenSporadicStandard.M22Std
