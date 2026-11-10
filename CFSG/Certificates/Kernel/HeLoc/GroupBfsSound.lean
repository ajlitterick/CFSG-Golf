module

public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import CFSG.RankThree.Native.PermEnumeration
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

namespace CFSG.KC.HeLoc

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

variable {n : Nat}

theorem enumOK_of_reach {gs : Array (Array Nat)} {ps : List Nat} {fuel N : Nat}
    {U : Nat → Array Nat} (hN : 0 < N)
    (hval : ∀ i < N, validA n (U i) = true) (h0 : ∃ i < N, U i = idA n)
    (hclos : ∀ i < N, ∀ k < gs.size, ∃ j < N, compA n gs[k]! (U i) = U j)
    (hkey : ∀ a < N, ∀ b < N, keyA n ps (U a) = keyA n ps (U b) → a = b)
    (hreach : ∀ i < N, CFSG.KC.Bfs.Reach (leftA n gs) gs.size (idA n) (U i))
    (hgv : ∀ k < gs.size, validA n gs[k]! = true) (hfuel : N ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true ∧ (enumBfs n gs ps fuel).pts.size = N := by
  set S : Finset (Array Nat) := (Finset.range N).image U with hSdef
  have hmemS : ∀ x, x ∈ S ↔ ∃ i < N, U i = x := fun x => by simp [hSdef]
  have hinj : Set.InjOn U (Finset.range N : Set Nat) := fun a ha b hb e =>
    hkey a (by simpa using ha) b (by simpa using hb) (by rw [e])
  have hS : ∀ x, CFSG.KC.Bfs.Reach (leftA n gs) gs.size (idA n) x ↔ x ∈ S := by
    intro x
    constructor
    · intro h
      induction h with
      | root =>
        obtain ⟨i, hi, e⟩ := h0
        exact (hmemS _).2 ⟨i, hi, e⟩
      | step k hk _ ih =>
        obtain ⟨i, hi, rfl⟩ := (hmemS _).1 ih
        obtain ⟨j, hj, e⟩ := hclos i hi k hk
        exact (hmemS _).2 ⟨j, hj, e.symm⟩
    · intro h
      obtain ⟨i, hi, rfl⟩ := (hmemS _).1 h
      exact hreach i hi
  have hv : ∀ x ∈ S, validA n x = true := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := (hmemS _).1 hx
    exact hval i hi
  have hk : ∀ x ∈ S, ∀ y ∈ S, keyA n ps x = keyA n ps y → x = y := by
    intro x hx y hy e
    obtain ⟨a, ha, rfl⟩ := (hmemS _).1 hx
    obtain ⟨b, hb, rfl⟩ := (hmemS _).1 hy
    rw [hkey a ha b hb e]
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injOn hinj]
    exact Finset.card_range N
  have hcf : S.card ≤ fuel := by rw [hcard]; exact hfuel
  have hspec := CFSG.KC.Bfs.arrBfs_spec (fuel := fuel) S hS hv hk hcf
  refine ⟨?_, by unfold enumBfs; rw [hspec.2.2.1, hcard]⟩
  unfold enumOK enumBfs
  rw [hspec.1, Bool.and_true, allLt_iff]
  exact hgv


end CFSG.KC.HeLoc

end
