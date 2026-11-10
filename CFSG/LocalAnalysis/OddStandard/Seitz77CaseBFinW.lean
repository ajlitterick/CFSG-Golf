module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow
public import CFSG.LinearAlgebra.LinearGroups.Generation
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.OddStandard.Seitz77.CaseBFin

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification.PSL3Four
  CFSG.OddStandard.Seitz77.L34
open scoped commutatorElement

private theorem F4_two : (2 : F4) = 0 := by
  have : ((2 : ℕ) : F4) = 0 := CharP.cast_eq_zero F4 2
  exact_mod_cast this

private theorem neg_one_F4 : (-1 : F4) = 1 := by
  rw [neg_eq_iff_add_eq_zero]
  linear_combination F4_two

@[expose] def weyl2 : SpecialLinearGroup (Fin 2) F4 :=
  ⟨!![0, 1; 1, 0], by simpa [Matrix.det_fin_two] using neg_one_F4⟩

@[expose] def weylS1 : SpecialLinearGroup (Fin 3) F4 := leviTwo F4 weyl2

@[expose] def weylS2 : SpecialLinearGroup (Fin 3) F4 := leviOne F4 weyl2

theorem coe_weylS1 : (weylS1 : Matrix (Fin 3) (Fin 3) F4) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [weylS1, coe_leviTwo]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weyl2]

theorem coe_weylS2 : (weylS2 : Matrix (Fin 3) (Fin 3) F4) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  rw [weylS2, coe_leviOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weyl2]

theorem weylS1_mem_range : weylS1 ∈ (leviTwo F4).range := ⟨weyl2, rfl⟩

theorem weylS2_mem_range : weylS2 ∈ (leviOne F4).range := ⟨weyl2, rfl⟩


theorem weyl_braid : weylS1 * weylS2 * weylS1 = weylS2 * weylS1 * weylS2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS1, coe_weylS2, Matrix.mul_apply, Fin.sum_univ_three]


section Generation

variable (K : Type) [Field K]


end Generation

section Torus


theorem weylS2_mul_unipU (a c : F4) :
    weylS2 * unipU F4 a 0 c = unipU F4 c 0 a * weylS2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS2, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylS1_mul_unipU (b c : F4) :
    weylS1 * unipU F4 0 b c = unipU F4 0 c b * weylS1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS1, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]


section Counts


end Counts

end Torus

end CFSG.OddStandard.Seitz77.CaseBFin
