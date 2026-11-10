module

public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]


theorem trace_low_up [CharP K 2] (a b : K) :
    ((MinData.Valid.slLower K a * MinData.Valid.slUpper K b :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = a * b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val, MinData.Valid.slUpper_val,
    Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h2

theorem slLower_mul_slUpper_apply_10 (a b : K) :
    ((MinData.Valid.slLower K a * MinData.Valid.slUpper K b :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = a := by
  rw [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val, MinData.Valid.slUpper_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end CFSG.RankThree.GF2n.Smith81.E7Model
