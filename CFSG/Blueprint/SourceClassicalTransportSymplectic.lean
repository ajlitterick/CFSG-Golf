module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix
open LinearMap (BilinForm)

section Isometry

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] def matrixIsometry (G : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {A | (A : Matrix ι ι K)ᵀ * G * A = G}
  mul_mem' {A B} hA hB := by
    change ((A * B : GL ι K) : Matrix ι ι K)ᵀ * G * ((A * B : GL ι K) : Matrix ι ι K) = G
    rw [Units.val_mul, transpose_mul]
    calc (B : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ * G * ((A : Matrix ι ι K) * B)
        = (B : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * G * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hA, hB]
  one_mem' := by
    change ((1 : GL ι K) : Matrix ι ι K)ᵀ * G * ((1 : GL ι K) : Matrix ι ι K) = G
    rw [Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' {A} hA := by
    change ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * G * ((A⁻¹ : GL ι K) : Matrix ι ι K) = G
    have h1 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * G * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * G * A) *
            ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA]
      _ = ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * G *
            ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, transpose_one, Matrix.one_mul, Matrix.mul_one]


end Isometry

abbrev sourceSpJ (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 1 (-1) 0

theorem statedSp_eq_matrixIsometry (n : ℕ) (K : Type) [Field K] :
    StatedSp n K = matrixIsometry (sourceSpJ n K) := by
  rw [StatedSp]
  exact Subgroup.closure_eq (matrixIsometry (sourceSpJ n K))


end CFSG.Blueprint.EvenSource
