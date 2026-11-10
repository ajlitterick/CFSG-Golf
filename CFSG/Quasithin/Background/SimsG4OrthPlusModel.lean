module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Quasithin.Background.SimsG4OrthURefl

public section

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.Quasithin.G11.P3Ortho.Om4

namespace CFSG.Quasithin.SimsG4.OrthPlus

section Matrices

variable {K : Type} [Field K]


theorem adjugate_adjugate_two (X : Matrix (Fin 2) (Fin 2) K) : X.adjugate.adjugate = X := by
  rw [Matrix.adjugate_fin_two X, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


variable [CharP K 2]

theorem refl_det_eq (s X : Matrix (Fin 2) (Fin 2) K) (hs : s.det = 1) :
    X + QuadraticMap.polar (determinantForm K) X s • s = s * X.adjugate * s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hs
  rw [determinantForm_polar, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination X 0 0 * hs + X 0 0 * h2
  · linear_combination X 0 1 * hs + X 0 1 * h2
  · linear_combination X 1 0 * hs + X 1 0 * h2
  · linear_combination X 1 1 * hs + X 1 1 * h2

end Matrices

section Conj


end Conj

section Rho


include hψ


end Rho

section Iso


include hψ


end Iso

end CFSG.Quasithin.SimsG4.OrthPlus
