module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCoverRootCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open Matrix CFSG.ShultStronglyClosedTI
open scoped MatrixGroups

universe u

variable {K : Type u} [Field K]

@[expose] def linearRootBorel (K : Type u) [Field K] :
    Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {A | A.val 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    change A.val 1 0 = 0 at hA
    change B.val 1 0 = 0 at hB
    change (A.val * B.val) 1 0 = 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [hA, hB, zero_mul, mul_zero, add_zero]
  inv_mem' := by
    intro A hA
    change A.val 1 0 = 0 at hA
    change (A⁻¹).val 1 0 = 0
    rw [SpecialLinearGroup.SL2_inv_expl]
    change -A.val 1 0 = 0
    rw [hA, neg_zero]

theorem linearRootBorel_diagonal (A : linearRootBorel K) :
    A.val.val 0 0 ≠ 0 ∧ A.val.val 1 1 = (A.val.val 0 0)⁻¹ := by
  have hA10 : A.val.val 1 0 = 0 := A.property
  have hdet : A.val.val 0 0 * A.val.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hA10, mul_zero, sub_zero] using A.val.property
  have hne : A.val.val 0 0 ≠ 0 := by
    intro h
    simp [h] at hdet
  exact ⟨hne, eq_inv_of_mul_eq_one_right hdet⟩

@[expose] def linearRootBorelMatrix (a : Kˣ) (b : K) :
    linearRootBorel K :=
  ⟨⟨!![(a : K), b; 0, ((a⁻¹ : Kˣ) : K)], by
      simp [Matrix.det_fin_two]⟩, by change (0 : K) = 0; rfl⟩

theorem linearRootBorel_matrix_parameters (A : linearRootBorel K) :
    linearRootBorelMatrix (Units.mk0 (A.val.val 0 0) (linearRootBorel_diagonal A).1)
      (A.val.val 0 1) = A := by
  have hA10 : A.val.val 1 0 = 0 := A.property
  apply Subtype.ext
  apply Subtype.ext
  change !![A.val.val 0 0, A.val.val 0 1; 0, (A.val.val 0 0)⁻¹] = A.val.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hA10, (linearRootBorel_diagonal A).2]

@[expose] def linearRootBorelParameterEquiv : linearRootBorel K ≃ Kˣ × K where
  toFun A := (Units.mk0 (A.val.val 0 0) (linearRootBorel_diagonal A).1, A.val.val 0 1)
  invFun p := linearRootBorelMatrix p.1 p.2
  left_inv := linearRootBorel_matrix_parameters
  right_inv p := by
    apply Prod.ext
    · apply Units.ext
      rfl
    · rfl


theorem linearRootBorel_conj_root (A : linearRootBorel K) (t : K) :
    A.val * linearCoverRoot t * A.val⁻¹ =
      linearCoverRoot ((A.val.val 0 0) ^ 2 * t) := by
  have hne := (linearRootBorel_diagonal A).1
  have hdiag := (linearRootBorel_diagonal A).2
  have hA10 : A.val.val 1 0 = 0 := A.property
  rw [SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change (A.val.val * !![1, t; 0, 1]) *
    !![A.val.val 1 1, -A.val.val 0 1; -A.val.val 1 0, A.val.val 0 0] =
      !![1, (A.val.val 0 0) ^ 2 * t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, hA10, hdiag, hne, pow_two]
  ring

theorem linear_root_normalizer_eq_borel [Finite K] :
    Subgroup.normalizer (linearCoverRootSubgroup K :
      Set (SpecialLinearGroup (Fin 2) K)) = linearRootBorel K := by
  apply le_antisymm
  · intro A hA
    have hroot : linearCoverRoot (1 : K) ∈ linearCoverRootSubgroup K :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hA (linearCoverRoot (1 : K))).mp hroot
    obtain ⟨t, ht⟩ := hconj
    have hzero : (A * linearCoverRoot (1 : K) * A⁻¹).val 1 0 = 0 := by
      rw [← ht]
      rfl
    have hentry : (A * linearCoverRoot (1 : K) * A⁻¹).val 1 0 = -(A.val 1 0) ^ 2 := by
      rw [SpecialLinearGroup.SL2_inv_expl]
      change ((A.val * !![1, (1 : K); 0, 1]) *
        !![A.val 1 1, -A.val 0 1; -A.val 1 0, A.val 0 0]) 1 0 = -(A.val 1 0) ^ 2
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    change A.val 1 0 = 0
    have hsq : (A.val 1 0) ^ 2 = 0 := neg_eq_zero.mp (hentry.symm.trans hzero)
    exact sq_eq_zero_iff.mp hsq
  · intro A hA
    apply Subgroup.mem_normalizer_fintype
    intro B hB
    obtain ⟨t, ht⟩ := hB
    rw [← ht]
    change A * linearCoverRoot t.toAdd * A⁻¹ ∈ linearCoverRootSubgroup K
    rw [linearRootBorel_conj_root (⟨A, hA⟩ : linearRootBorel K)]
    exact ⟨Multiplicative.ofAdd ((A.val 0 0) ^ 2 * t.toAdd), rfl⟩

theorem linear_root_normalizer_card [Finite K] :
    Nat.card (Subgroup.normalizer (linearCoverRootSubgroup K :
      Set (SpecialLinearGroup (Fin 2) K))) = (Nat.card K - 1) * Nat.card K := by
  rw [linear_root_normalizer_eq_borel]
  calc
    Nat.card (linearRootBorel K) = Nat.card (Kˣ × K) :=
      Nat.card_congr linearRootBorelParameterEquiv
    _ = (Nat.card K - 1) * Nat.card K := by rw [Nat.card_prod, Nat.card_units]

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
