module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized
public import CFSG.LocalAnalysis.ComponentInitial.BinaryQuadraticRefinement

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

section Space

variable (V K : Type*) [AddCommGroup V] [Field K]


variable {V K}


end Space

section Monomials

variable {K : Type*} [Field K] [CharP K 2]


end Monomials

theorem sum_sum_eq_sum_le {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → M) :
    ∑ i, ∑ j, F i j = ∑ p : {p : Fin n × Fin n // p.1 ≤ p.2},
      if p.1.1 = p.1.2 then F p.1.1 p.1.2 else F p.1.1 p.1.2 + F p.1.2 p.1.1 := by
  classical
  rw [← Finset.sum_subtype (p := fun p : Fin n × Fin n => p.1 ≤ p.2)
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2) (fun p => by simp)
      (fun p : Fin n × Fin n => if p.1 = p.2 then F p.1 p.2 else F p.1 p.2 + F p.2 p.1),
    Finset.sum_filter, ← Fintype.sum_prod_type' F]
  have hswap : ∑ p : Fin n × Fin n, (if p.2 < p.1 then F p.1 p.2 else 0) =
      ∑ p : Fin n × Fin n, (if p.1 < p.2 then F p.2 p.1 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => rfl
  calc ∑ p : Fin n × Fin n, F p.1 p.2
      = ∑ p : Fin n × Fin n,
          ((if p.1 ≤ p.2 then F p.1 p.2 else 0) + (if p.2 < p.1 then F p.1 p.2 else 0)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p.1 ≤ p.2
        · simp [h, not_lt.2 h]
        · simp [h, not_le.1 h]
    _ = ∑ p : Fin n × Fin n,
          ((if p.1 ≤ p.2 then F p.1 p.2 else 0) + (if p.1 < p.2 then F p.2 p.1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hswap]
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · simp [h.le, h.ne, h]
        · simp [h]
        · simp [not_le.2 h, not_lt.2 h.le]


section Criterion

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem exists_sq_eq (y : K) : ∃ x : K, x ^ 2 = y := by
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 (frobenius_inj K 2)) y
  exact ⟨x, by rwa [frobenius_def] at hx⟩

theorem coeff_eq_zero_of_forall_sum_sum_eq_zero {n : ℕ} (hn : 2 ^ (n - 1) < Fintype.card K)
    {C : Fin n → Fin n → K}
    (hC : ∀ x : K, ∑ i, ∑ j, C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) = 0) :
    (∀ i j, C i j + C j i = 0) ∧ ∀ i, C i i = 0 := by
  have hpol : ∀ x y : K,
      ∑ i, ∑ j, (C i j + C j i) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) = 0 := by
    intro x y
    have e : ∀ i j : Fin n, C i j * ((x + y) ^ 2 ^ (i : ℕ) * (x + y) ^ 2 ^ (j : ℕ)) =
        C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) +
          C i j * (y ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) +
          (C i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) +
            C i j * (y ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ))) := fun i j => by
      rw [add_pow_char_pow, add_pow_char_pow]
      ring
    have hswap : ∑ i, ∑ j, C i j * (y ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) =
        ∑ i, ∑ j, C j i * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h := hC (x + y)
    simp only [e, Finset.sum_add_distrib, hC x, hC y, zero_add, hswap] at h
    rw [← h]
    simp only [add_mul, Finset.sum_add_distrib]
  have hsym : ∀ i j, C i j + C j i = 0 := fun i j =>
    congrFun (congrFun (eq_zero_of_forall_sum_sum_mul_pow_eq_zero hn hpol) i) j
  refine ⟨hsym, ?_⟩
  have hdiag : ∀ x : K, ∑ i, C i i * (x ^ 2) ^ 2 ^ (i : ℕ) = 0 := by
    intro x
    rw [← hC x]
    have e1 : ∑ i, C i i * (x ^ 2) ^ 2 ^ (i : ℕ) =
        ∑ i, ∑ j, if i = j then C i j * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (j : ℕ)) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), ← pow_mul, ← pow_add, ← two_mul,
        ← pow_succ', pow_succ]
    rw [e1, sum_sum_eq_sum_le, sum_sum_eq_sum_le]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1.1 = p.1.2
    · simp [h]
    · have h0 : C p.1.1 p.1.2 * (x ^ 2 ^ (p.1.1 : ℕ) * x ^ 2 ^ (p.1.2 : ℕ)) +
          C p.1.2 p.1.1 * (x ^ 2 ^ (p.1.2 : ℕ) * x ^ 2 ^ (p.1.1 : ℕ)) = 0 := by
        rw [mul_comm (x ^ 2 ^ (p.1.2 : ℕ)), ← add_mul, hsym, zero_mul]
      simp [h, Ne.symm h, h0]
  intro i
  have h := eq_zero_of_forall_sum_mul_pow_eq_zero hn (a := fun i => C i i) fun y => by
    obtain ⟨x, rfl⟩ := exists_sq_eq y
    exact hdiag x
  exact congrFun h i

end Criterion

section Unary


end Unary

section Binary


end Binary


end CFSG.LocalAnalysis.ComponentInitial
