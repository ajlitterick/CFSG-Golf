module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

def IsOrthGL (B : GL (Fin n) (ZMod 2)) : Prop :=
  (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1

theorem IsOrthGL.transpose_eq_inv {B : GL (Fin n) (ZMod 2)} (hB : IsOrthGL B) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  calc (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
      = (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (B : Matrix (Fin n) (Fin n) (ZMod 2))) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
        rw [Matrix.mul_assoc, hB, Matrix.mul_one]

theorem IsOrthGL.dotProduct_mulVec_mulVec {B : GL (Fin n) (ZMod 2)} (hB : IsOrthGL B)
    (x y : Fin n → ZMod 2) :
    ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) ⬝ᵥ ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) =
      x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    hB.transpose_eq_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]


end CFSG.ASVolI.ChH
