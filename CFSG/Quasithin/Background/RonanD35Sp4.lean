module

public import CFSG.Quasithin.Background.RonanD35

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin CFSG.Open
open scoped Matrix

section Matrices

variable {K : Type} [Field K]

@[expose] def sp4Mat (S : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 S 0 1

theorem sp4Mat_mul (S S' : Matrix (Fin 2) (Fin 2) K) :
    sp4Mat S * sp4Mat S' = sp4Mat (S + S') := by
  simp only [sp4Mat, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  rw [add_comm S' S]

theorem sp4Mat_zero : sp4Mat (0 : Matrix (Fin 2) (Fin 2) K) = 1 :=
  Matrix.fromBlocks_one

theorem sp4Mat_mul_neg (S : Matrix (Fin 2) (Fin 2) K) : sp4Mat S * sp4Mat (-S) = 1 := by
  rw [sp4Mat_mul, add_neg_cancel, sp4Mat_zero]


theorem sp4Mat_symplectic {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    (sp4Mat S)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sp4Mat S = Matrix.fromBlocks 0 1 (-1) 0 := by
  simp [sp4Mat, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hS]

@[expose] def sp4GL (S : Matrix (Fin 2) (Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K where
  val := sp4Mat S
  inv := sp4Mat (-S)
  val_inv := sp4Mat_mul_neg S
  inv_val := by rw [sp4Mat_mul, neg_add_cancel, sp4Mat_zero]

@[expose] def sp4Elt {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) : ↥(StatedSp 2 K) :=
  ⟨sp4GL S, Subgroup.subset_closure (sp4Mat_symplectic hS)⟩

@[simp] theorem sp4Elt_coe {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    (((sp4Elt hS : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4Mat S :=
  rfl


end Matrices

section Radical


end Radical

section Covering


end Covering


end CFSG.Quasithin.RonanD35
