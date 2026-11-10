module

public import CFSG.GroupTheory.KleinFourAutomorphism
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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

namespace ReciprocalFusion

theorem card_sup_eq_mul_of_disjoint (A B : Subgroup X) (hnormal : B ≤ normalizer (A : Set X))
    (hdisjoint : Disjoint A B) : Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↑(A ⊔ B) := fun z =>
    ⟨(z.1 : X) * (z.2 : X), mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    exact mul_injective_of_disjoint hdisjoint (congrArg Subtype.val hxy)
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : X) ∈ (A : Set X) * (B : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card (A ⊔ B : Subgroup X) = Nat.card (A × B) :=
        Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

theorem eq_one_or_eq_of_mem_zpowers [Finite X] {a x : X} (ha : orderOf a = 2)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  interval_cases k <;> simp

theorem isKleinFour_closure_pair [Finite X] {a t : X} (ha : orderOf a = 2) (ht : orderOf t = 2)
    (hcomm : a * t = t * a) (hne : a ≠ t) : IsKleinFour (closure {a, t}) := by
  have hcl : closure {a, t} = zpowers a ⊔ zpowers t := by
    rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hnorm : zpowers t ≤ normalizer (zpowers a : Set X) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left hcomm k)).eq
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by decide)
  have hdisj : Disjoint (zpowers a) (zpowers t) := by
    rw [disjoint_def]
    intro x hxa hxt
    rcases eq_one_or_eq_of_mem_zpowers ha hxa with h | rfl
    · exact h
    · rcases eq_one_or_eq_of_mem_zpowers ht hxt with h | h
      · exact h
      · exact absurd h hne
  have hcard : Nat.card (closure {a, t}) = 4 := by
    rw [hcl, card_sup_eq_mul_of_disjoint _ _ hnorm hdisj, Nat.card_zpowers, Nat.card_zpowers,
      ha, ht]
  have hsq : ∀ v : closure {a, t}, v ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    have hv' : v ∈ ((zpowers a ⊔ zpowers t : Subgroup X) : Set X) := by
      rw [← hcl]
      exact hv
    rw [coe_mul_of_right_le_normalizer_left _ _ hnorm] at hv'
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hv'
    have hxy : Commute x y := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left hcomm i).zpow_right j
    have hx2 : x ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ha hx with rfl | rfl
      · exact one_pow 2
      · rw [← ha]; exact pow_orderOf_eq_one _
    have hy2 : y ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ht hy with rfl | rfl
      · exact one_pow 2
      · rw [← ht]; exact pow_orderOf_eq_one _
    change (x * y) ^ 2 = 1
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent (closure {a, t}) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have hsub := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : closure {a, t})
    omega
  · exact h

theorem mem_normalizer_closure_pair [Finite X] {a t g : X} (ha : g * a * g⁻¹ ∈ closure {a, t})
    (ht : g * t * g⁻¹ ∈ closure {a, t}) : g ∈ normalizer (closure {a, t} : Set X) := by
  apply mem_normalizer_fintype
  intro n hn
  have hle : closure {a, t} ≤ (closure {a, t}).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · simpa [MulAut.conj_apply] using ha
    · simpa [MulAut.conj_apply] using ht
  simpa [MulAut.conj_apply] using hle hn


end ReciprocalFusion

open ReciprocalFusion


end CFSG.ComponentClassification.UnbalancedGS
