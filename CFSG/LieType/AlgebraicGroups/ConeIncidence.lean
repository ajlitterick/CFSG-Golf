module

public import CFSG.LieType.AlgebraicGroups.ClosedCone
public import CFSG.Mathlib.RingTheory.HomogeneousElimination
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

public noncomputable section

open WithConv TauCeti.Comodule MvPolynomial

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k]

theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {p : MvPolynomial σ k} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : k) (v : σ → k) :
    eval (c • v) p = c ^ d * eval v p := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m i = d := by
    by_contra h
    exact (mem_support_iff.mp hm) (hp.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hmd]
  ring

theorem eval_homogeneousComponent_eq_zero [Infinite k] {σ : Type*} [Fintype σ]
    {f : MvPolynomial σ k} {v : σ → k} (h : ∀ c : k, eval (c • v) f = 0) (n : ℕ) :
    eval v (homogeneousComponent n f) = 0 := by
  rcases lt_or_ge f.totalDegree n with hn | hn
  · rw [homogeneousComponent_eq_zero n f hn, map_zero]
  let Q : Polynomial k := ∑ e ∈ Finset.range (f.totalDegree + 1),
    Polynomial.monomial e (eval v (homogeneousComponent e f))
  have hQ : Q = 0 := by
    refine Polynomial.funext fun c => ?_
    rw [Polynomial.eval_zero, ← h c]
    conv_rhs => rw [← sum_homogeneousComponent f]
    rw [map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.eval_monomial,
      eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e f), mul_comm]
  have hcoeff := congrArg (fun q : Polynomial k => q.coeff n) hQ
  simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero,
    Finset.sum_ite_eq', Finset.mem_range] at hcoeff
  rwa [if_pos (Nat.lt_succ_of_le hn)] at hcoeff

theorem IsZariskiClosed.exists_isHomogeneous [Infinite k] {V : Type v} [AddCommGroup V]
    [Module k V] {X : Set V} (hX : IsZariskiClosed k X) (hc : IsCone k X) {σ : Type*}
    [Fintype σ] (b : Module.Basis σ k V) :
    ∃ S : Set (MvPolynomial σ k), (∀ f ∈ S, ∃ n, f.IsHomogeneous n) ∧
      ∀ x, x ∈ X ↔ ∀ f ∈ S, eval (b.equivFun x) f = 0 := by
  obtain ⟨I, hI⟩ := hX.exists_eq_preimage_zeroLocus b
  refine ⟨{p | ∃ f ∈ I, ∃ n, p = homogeneousComponent n f}, ?_, fun x => ⟨fun hx => ?_,
    fun hx => ?_⟩⟩
  · rintro _ ⟨f, -, n, rfl⟩
    exact ⟨n, homogeneousComponent_isHomogeneous n f⟩
  · rintro _ ⟨f, hf, n, rfl⟩
    refine eval_homogeneousComponent_eq_zero (fun c => ?_) n
    have hcx : c • x ∈ X := hc c x hx
    rw [hI, Set.mem_preimage, mem_zeroLocus_iff, map_smul] at hcx
    exact hcx f hf
  · rw [hI, Set.mem_preimage, mem_zeroLocus_iff]
    intro f hf
    change eval (b.equivFun x) f = 0
    rw [← sum_homogeneousComponent f, map_sum]
    exact Finset.sum_eq_zero fun e _ => hx _ ⟨f, hf, e, rfl⟩


end CFSG.LieType.AlgebraicGroups.ClosedCone
