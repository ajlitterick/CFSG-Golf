module

public import CFSG.LinearAlgebra.AnisotropicBinaryPlane
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
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

namespace CFSG.LocalAnalysis

open Module Polynomial

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [Field E] [Algebra K E]

theorem natCard_eq_sq_of_finrank_eq_two (hE : finrank K E = 2) :
    Nat.card E = Fintype.card K ^ 2 := by
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  rw [Module.natCard_eq_pow_finrank (K := K), hE, Nat.card_eq_fintype_card]

theorem pow_card_eq_self_iff (hE : finrank K E = 2) (z : E) :
    z ^ Fintype.card K = z ↔ z ∈ (algebraMap K E).range := by
  classical
  constructor
  · intro hz
    have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
    have : Finite E := Module.finite_of_finite K
    let := Fintype.ofFinite E
    have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
    set S := Finset.univ.filter fun w : E => w ^ Fintype.card K = w
    have hS : S.card ≤ Fintype.card K := by
      have hne := FiniteField.X_pow_card_sub_X_ne_zero E hq1
      calc S.card ≤ (X ^ Fintype.card K - X : E[X]).roots.toFinset.card := by
            refine Finset.card_le_card fun w hw => ?_
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X,
              sub_eq_zero]
            exact (Finset.mem_filter.mp hw).2
        _ ≤ (X ^ Fintype.card K - X : E[X]).roots.card := Multiset.toFinset_card_le _
        _ ≤ (X ^ Fintype.card K - X : E[X]).natDegree := card_roots' _
        _ = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq E hq1
    have himg : Finset.univ.image (algebraMap K E) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hw
        rw [Finset.mem_filter, ← map_pow, FiniteField.pow_card]
        exact ⟨Finset.mem_univ _, rfl⟩
      · rw [Finset.card_image_of_injective _ (algebraMap K E).injective, Finset.card_univ]
        exact hS
    have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    rw [← himg] at hzS
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hzS
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

theorem eq_pow_card_of_ne_one (hE : finrank K E = 2) {σ : E ≃ₐ[K] E} (hσ : σ ≠ 1) (z : E) :
    σ z = z ^ Fintype.card K := by
  classical
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional K E := this
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic K E
  have hφ : ∀ w, φ w = w ^ Fintype.card K := fun w => by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hφ1 : φ ≠ 1 := by
    intro h
    have hall : ∀ w : E, w ∈ (algebraMap K E).range := fun w => by
      rw [← pow_card_eq_self_iff hE, ← hφ, h, AlgEquiv.one_apply]
    have hsurj : Function.Surjective (algebraMap K E) := fun w => hall w
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [natCard_eq_sq_of_finrank_eq_two hE, Nat.card_eq_fintype_card] at h1
    nlinarith
  by_contra hne
  have hσφ : σ ≠ φ := fun h => hne (by rw [h, hφ])
  have hcard := AlgEquiv.card_le (F := K) (K := E)
  rw [hE] at hcard
  have h3 : ({1, σ, φ} : Finset (E ≃ₐ[K] E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hσφ]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσ h.symm, fun h => hφ1 h.symm⟩
  have h4 := Finset.card_le_univ ({1, σ, φ} : Finset (E ≃ₐ[K] E))
  omega


variable [CharP K 2]


theorem exists_root_quadratic (hE : finrank K E = 2) {ε : K}
    (hQ : ∀ x y : K, x ^ 2 + ε * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0) :
    ∃ ζ : E, ζ ^ 2 + algebraMap K E ε * ζ + 1 = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : Fact (∀ r : K, r ^ 2 ≠ 1 + ε * r) :=
    ⟨CFSG.LinearAlgebra.sq_ne_one_add_mul_of_anisotropic hQ⟩
  let : Fintype (QuadraticAlgebra K 1 ε) :=
    Fintype.ofEquiv (K × K) (QuadraticAlgebra.equivProd 1 ε).symm
  have hLcard : Fintype.card (QuadraticAlgebra K 1 ε) = Fintype.card K ^ 2 := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd 1 ε), Fintype.card_prod, sq]
  set ω : QuadraticAlgebra K 1 ε := ⟨0, 1⟩
  set f : K[X] := X ^ 2 + C ε * X + 1 with hf
  have hf_monic : f.Monic := by
    rw [hf]
    monicity!
  have hf_deg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hf_irr : Irreducible f := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hf_deg]; decide) fun r h => ?_
    have h1 := hQ r 1 (by
      have h3 : f.eval r = 0 := h
      simpa [hf] using h3)
    exact one_ne_zero h1.2
  have hω : aeval ω f = 0 := by
    simp only [hf, map_add, map_mul, map_pow, aeval_X, aeval_C, map_one]
    ext
    · simp [ω, pow_two, QuadraticAlgebra.re_one]
      linear_combination h2
    · simp [ω, pow_two, QuadraticAlgebra.im_one]
      linear_combination ε * h2
  have hdvd : f ∣ X ^ (Fintype.card K ^ 2) - X := by
    rw [minpoly.eq_of_irreducible_of_monic hf_irr hω hf_monic]
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, ← hLcard, FiniteField.pow_card, sub_self]
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : Finite E := Module.finite_of_finite K
  let := Fintype.ofFinite E
  have hEcard : Fintype.card E = Fintype.card K ^ 2 := by
    rw [← Nat.card_eq_fintype_card, natCard_eq_sq_of_finrank_eq_two hE]
  have hsplit := IsSplittingField.splits E (X ^ Fintype.card E - X : K[X])
  rw [hEcard] at hsplit
  have hq1 : 1 < Fintype.card K ^ 2 := by
    have := Fintype.one_lt_card (α := K)
    nlinarith
  have hne : (X ^ (Fintype.card K ^ 2) - X : K[X]).map (algebraMap K E) ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X]
    exact FiniteField.X_pow_card_sub_X_ne_zero E hq1
  have hfsplit := hsplit.of_dvd hne (Polynomial.map_dvd _ hdvd)
  obtain ⟨ζ, hζ⟩ := hfsplit.exists_eval_eq_zero (by
    rw [degree_map, Polynomial.degree_eq_natDegree hf_monic.ne_zero, hf_deg]
    decide)
  refine ⟨ζ, ?_⟩
  simpa [hf] using hζ


end CFSG.LocalAnalysis
