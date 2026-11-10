module

public import CFSG.Blueprint.CatalogGenerators

public section

namespace CFSG.Blueprint

variable {K : Type} [Field K]

theorem suzukiW_eq_permMatrix :
    suzukiW K = (Fin.revPerm : Equiv.Perm (Fin 4)).permMatrix K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Equiv.Perm.permMatrix, PEquiv.toMatrix]

theorem det_suzukiW_eq_one : (suzukiW K).det = 1 := by
  rw [suzukiW_eq_permMatrix, Matrix.det_permutation]
  have h : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 4)) = 1 := by decide
  rw [h]
  simp


end CFSG.Blueprint
