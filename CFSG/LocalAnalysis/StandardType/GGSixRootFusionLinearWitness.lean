module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Witness

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem diagonal_mul_ggInvMatrix_comm {l : ℕ} (d : Fin n → F)
    (hd : ∀ a b : Fin n, (b : ℕ) < l → (a : ℕ) = b + (n - l) → d a = d b) :
    Matrix.diagonal d * ggInvMatrix n l F = ggInvMatrix n l F * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [ggInvMatrix, Matrix.add_apply, Matrix.one_apply, ggInvNil_apply]
  by_cases hab : a = b
  · subst hab
    ring
  · rw [ite_eq_right hab, zero_add]
    split_ifs with h
    · rw [mul_one, one_mul, hd a b h.1 h.2.1]
    · rw [mul_zero, zero_mul]


end Witness

end CFSG.StandardType
