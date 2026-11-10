module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.ChevalleyGenerators

public section

namespace CFSG.Blueprint

variable (a : ℕ) {K : Type} [Field K]

theorem det_suzukiS (u v : K) : (suzukiS a u v).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
  · simp [suzukiS, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [suzukiS]

theorem det_suzukiD (l : Kˣ) : (suzukiD a l).det = 1 := by
  have h : l ^ (1 + (2 ^ a : ℤ)) * l ^ (2 ^ a : ℤ) * l ^ (-(2 ^ a : ℤ)) *
      l ^ (-1 - (2 ^ a : ℤ)) = 1 := by
    rw [← zpow_add, ← zpow_add, ← zpow_add]
    ring_nf
    exact zpow_zero l
  rw [suzukiD, Matrix.det_diagonal, Fin.prod_univ_four]
  change ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (2 ^ a : ℤ) : Kˣ) : K) *
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = 1
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h, Units.val_one]

variable (K) in
theorem suzukiW_mul_self : suzukiW K * suzukiW K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]


end CFSG.Blueprint
