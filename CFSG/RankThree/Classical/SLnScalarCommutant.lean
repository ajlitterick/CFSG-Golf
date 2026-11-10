module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.Classical

open scoped Matrix

variable {M : Type*} [Field M]

@[expose] def naturalSL (k : Subfield M) (n : ℕ) : Subgroup (GL (Fin n) M) :=
  (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map k.subtype)).range

theorem exists_elementary_mem_naturalSL (k : Subfield M) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∃ X ∈ naturalSL k n, (X : Matrix (Fin n) (Fin n) M) = 1 + Matrix.single i j 1 := by
  refine ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k.subtype
    (⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩ :
      Matrix.SpecialLinearGroup (Fin n) k)), ⟨_, rfl⟩, ?_⟩
  change (Matrix.transvection i j (1 : k)).map k.subtype = 1 + Matrix.single i j 1
  ext a b
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem mem_range_scalar_of_commute_elementary {n : ℕ} (A : GL (Fin n) M)
    (h : ∀ i j : Fin n, i ≠ j →
      (1 + Matrix.single i j 1 : Matrix (Fin n) (Fin n) M) * (A : Matrix (Fin n) (Fin n) M) =
        (A : Matrix (Fin n) (Fin n) M) * (1 + Matrix.single i j 1)) :
    A ∈ (Matrix.GeneralLinearGroup.scalar (Fin n)).range := by
  have hcomm : Pairwise fun i j =>
      Commute (Matrix.single i j (1 : M)) (A : Matrix (Fin n) (Fin n) M) := by
    intro i j hij
    have h1 := h i j hij
    rw [add_mul, mul_add, one_mul, mul_one] at h1
    exact add_left_cancel h1
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, Units.ext ?_⟩
    ext i
    exact hn.elim i
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [← ha, map_zero, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact ha


theorem apply_eq_zero_of_conj_inv_transpose_elementary {n : ℕ} (A : GL (Fin n) M) {i j : Fin n}
    (h : (A : Matrix (Fin n) (Fin n) M) * (1 - Matrix.single j i 1) *
      (↑A⁻¹ : Matrix (Fin n) (Fin n) M) = 1 + Matrix.single i j 1) {l : Fin n} (hl : l ≠ i) :
    (A : Matrix (Fin n) (Fin n) M) l j = 0 := by
  have h2 : (A : Matrix (Fin n) (Fin n) M) * (1 - Matrix.single j i 1) =
      (1 + Matrix.single i j 1) * (A : Matrix (Fin n) (Fin n) M) := by
    rw [← h, Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin n) (Fin n) M), A.inv_mul, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h2
  have h3 := congrFun (congrFun h2 l) i
  have h4 : (Matrix.single i j (1 : M) * (A : Matrix (Fin n) (Fin n) M)) l i = 0 :=
    Matrix.single_mul_apply_of_ne (h := hl) ..
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_single_apply_same, h4] at h3
  linear_combination -h3


end CFSG.RankThree.Classical
