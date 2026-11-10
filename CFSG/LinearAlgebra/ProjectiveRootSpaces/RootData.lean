module

public import CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

open scoped MatrixGroups
open CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup


@[expose] noncomputable def diagonalSL (F : Type) [Field F] : Fˣ →* SL(2, F) where
  toFun a := ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show (!![((a * b : Fˣ) : F), 0; 0, (((a * b)⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]


variable {F : Type} [Field F]


theorem diagonalSL_apply_zero_zero (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := rfl

theorem diagonalSL_apply_one_one (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = ((a⁻¹ : Fˣ) : F) := rfl

theorem diagonalSL_apply_zero_one (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := rfl

theorem diagonalSL_apply_one_zero (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl


end CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData
