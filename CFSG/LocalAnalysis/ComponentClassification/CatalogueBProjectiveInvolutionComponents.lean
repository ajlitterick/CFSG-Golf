module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionNonsquareComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K : Type*} [Field K] [Finite K]

theorem projective_involution_centralizer_pComponent_quasisimple
    (n : ℕ) (hn : 2 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (htwo : (2 : K) ≠ 0) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hinvolution : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    (p : ℕ) (hp : p.Prime)
    (L : Subgroup (Subgroup.centralizer {Matrix.ProjGenLinGroup.mk A}))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinvolution
  by_cases hsquare : IsSquare lambda.val
  · exact square_projectiveCentralizer_pComponent_quasisimple
      n hn A lambda htwo hne hsq hsquare p hp L hL
  · exact nonsquare_projectiveCentralizer_pComponent_quasisimple
      n hn A lambda hsq hsquare p hp L hL


end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
