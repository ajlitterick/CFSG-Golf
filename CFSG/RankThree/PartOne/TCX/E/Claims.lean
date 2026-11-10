module

public import CFSG.RankThree.PartOne.TCX.E.Engine
public import CFSG.RankThree.PartOne.KLCE.TypeSU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.PartOne.KLCE.TypeSL

public section

namespace CFSG.RankThree.PartOne.TCX.E

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KLCE

section Abstract

@[expose] def LayerClaims2 (p : ℕ) {G : Type} [Group G] (α : MulAut G) (Q : Subgroup G) : Prop :=
  (∀ g ∈ Q, α g ∈ Q) ∧ (∀ e ∈ Q, ¬ ∀ g ∈ Q, α g = e * g * e⁻¹) ∧
    (∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
      LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f'')) ∧
    ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁


end Abstract

section Trace

variable {n : ℕ} {K : Type} [Field K]

theorem trace_conj_units (u : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    Matrix.trace ((u : Matrix (Fin n) (Fin n) K) * M * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      Matrix.trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

end Trace

section SL

variable {m : ℕ} {K' : Type} [Field K']

theorem trace_transvection_pair {i j : Fin (m + 2)} (hij : i ≠ j) (a b : K') :
    Matrix.trace (((SpecialLinearGroup.transvection hij a *
        SpecialLinearGroup.transvection hij.symm b : SpecialLinearGroup (Fin (m + 2)) K') :
        Matrix (Fin (m + 2)) (Fin (m + 2)) K')) = ((m + 2 : ℕ) : K') + a * b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, mul_add, add_mul, add_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.single_mul_single_same]
  simp [Matrix.trace_add, Matrix.trace_one, Matrix.trace_single_eq_of_ne _ _ _ hij,
    Matrix.trace_single_eq_of_ne _ _ _ hij.symm, Matrix.trace_single_eq_same]


end SL

section SU

variable {m : ℕ} {K : Type} [Field K] {g : ℕ}

theorem mem_statedSU_iff_n [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ g) ^ 2)
    (A : GL (Fin n) K) : A ∈ StatedSU n (2 ^ g) K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ 2 ^ g))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := n) hn).1
  have := Set.ext_iff.1 h A
  simpa using this

@[expose] noncomputable def permGLn [CharP K 2] {n : ℕ} (σ : Equiv.Perm (Fin n)) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix K) (by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])

omit [Field K] in
theorem coe_permGLn [Field K] [CharP K 2] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((permGLn σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ.permMatrix K := rfl

theorem map_pow_permMatrix_n {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix K).map (· ^ 2 ^ g) = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  split_ifs <;> simp [zero_pow (pow_ne_zero g (two_ne_zero))]

theorem permGLn_mem [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ g) ^ 2)
    (σ : Equiv.Perm (Fin n)) : permGLn σ ∈ StatedSU n (2 ^ g) K := by
  rw [mem_statedSU_iff_n hn hK, coe_permGLn, map_pow_permMatrix_n, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one, Matrix.det_permutation]
  refine ⟨?_, rfl⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simpa [h] using CharTwo.neg_eq (1 : K)

@[expose] def dvec (l : K) (i : Fin (m + 3)) : K := if i = 0 then l else if i = 1 then l⁻¹ else 1

theorem prod_dvec (l : K) (hl : l ≠ 0) : ∏ i : Fin (m + 3), dvec l i = 1 := by
  have h : ∀ i : Fin (m + 1), dvec l i.succ.succ = 1 := fun i => by
    simp [dvec, Fin.succ_ne_zero, Fin.succ_succ_ne_one]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Finset.prod_congr rfl (fun i _ => h i)]
  simp [dvec, hl]

theorem sum_dvec (l : K) : ∑ i : Fin (m + 3), dvec l i = l + l⁻¹ + ((m + 1 : ℕ) : K) := by
  have h : ∀ i : Fin (m + 1), dvec l i.succ.succ = 1 := fun i => by
    simp [dvec, Fin.succ_ne_zero, Fin.succ_succ_ne_one]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_congr rfl (fun i _ => h i)]
  simp [dvec, add_assoc]

@[expose] noncomputable def diagSU (l : Kˣ) : GL (Fin (m + 3)) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (dvec (l : K))) (by
    rw [Matrix.det_diagonal, prod_dvec _ l.ne_zero]
    exact one_ne_zero)

theorem coe_diagSU (l : Kˣ) :
    ((diagSU l : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K) =
      Matrix.diagonal (dvec (l : K)) := rfl

theorem diagSU_mem [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) (l : Kˣ)
    (hl : l ^ (2 ^ g + 1) = 1) : (diagSU l : GL (Fin (m + 3)) K) ∈ StatedSU (m + 3) (2 ^ g) K := by
  have hl' : (l : K) ^ (2 ^ g + 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hl
    simpa using this
  rw [mem_statedSU_iff_n (by omega) hK, coe_diagSU, Matrix.det_diagonal,
    prod_dvec _ l.ne_zero]
  refine ⟨rfl, ?_⟩
  rw [Matrix.diagonal_map (by simp [zero_pow (pow_ne_zero g two_ne_zero)]),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h0 : (l : K) ≠ 0 := l.ne_zero
  by_cases hi0 : i = 0
  · subst hi0
    simpa [dvec, ← pow_succ] using hl'
  · by_cases hi1 : i = 1
    · subst hi1
      simp only [dvec, hi0, ite_false, ite_true]
      rw [inv_pow, ← mul_inv, ← pow_succ, hl', inv_one]
    · simp [dvec, hi0, hi1]

end SU

section PermHelpers

variable {K : Type} [Field K] {n : ℕ}

theorem permMatrix_injective_n :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => σ.permMatrix K) := fun σ τ h => by
  have h1 : σ.toPEquiv = τ.toPEquiv := PEquiv.toMatrix_injective h
  refine Equiv.ext fun x => ?_
  have := congrArg (fun e : Fin n ≃. Fin n => e x) h1
  simpa [Equiv.toPEquiv_apply] using this


end PermHelpers

section SUClaims


end SUClaims

end CFSG.RankThree.PartOne.TCX.E
