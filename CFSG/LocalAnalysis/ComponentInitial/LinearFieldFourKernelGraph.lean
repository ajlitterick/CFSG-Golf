module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelStructure

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFourKernel

open Subgroup Matrix LinearFlag LinearFieldFour LinearCover CFSG.ComponentClassification
open scoped commutatorElement

section GraphField

variable {k : Type*} [Field k]

@[expose] def invTransposeSL : SpecialLinearGroup (Fin 3) k →* SpecialLinearGroup (Fin 3) k where
  toFun B := (B⁻¹).transpose
  map_one' := by
    rw [inv_one]
    apply Subtype.ext
    change (1 : Matrix (Fin 3) (Fin 3) k)ᵀ = 1
    exact transpose_one
  map_mul' A B := by
    apply Subtype.ext
    change (adjugate ((A : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k)))ᵀ =
      (adjugate (A : Matrix (Fin 3) (Fin 3) k))ᵀ * (adjugate (B : Matrix (Fin 3) (Fin 3) k))ᵀ
    rw [adjugate_mul_distrib, transpose_mul]

variable [CharP k 2]


@[expose] def jM : Matrix (Fin 3) (Fin 3) k := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def jMat : SpecialLinearGroup (Fin 3) k :=
  ⟨jM, by simp only [jM, det_fin_three]; simp [CharTwo.neg_eq]⟩

theorem jMat_mul_self : (jMat : SpecialLinearGroup (Fin 3) k) * jMat = 1 := by
  apply Subtype.ext
  change (jM : Matrix (Fin 3) (Fin 3) k) * jM = 1
  simp only [jM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


end GraphField


end LinearFieldFourKernel

end CFSG.LocalAnalysis.ComponentInitial
