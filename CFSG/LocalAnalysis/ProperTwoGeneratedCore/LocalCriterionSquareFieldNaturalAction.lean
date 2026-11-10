module

import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups

variable {F : Type u} [Field F]

theorem semilinearApply_mul (a b : Gamma F) (v : Fin 2 → F) :
    semilinearApply (a * b).left (a * b).right v =
      semilinearApply a.left a.right (semilinearApply b.left b.right v) := by
  have hmap : (fun j => a.right (semilinearApply b.left b.right v j)) =
      Matrix.mulVec (a.right.toRingHom.mapMatrix
        (b.left : Matrix (Fin 2) (Fin 2) F)) (fun j => a.right (b.right (v j))) := by
    ext j
    exact a.right.toRingHom.map_mulVec (b.left : Matrix (Fin 2) (Fin 2) F)
      (fun k => b.right (v k)) j
  change Matrix.mulVec ((a * b).left : Matrix (Fin 2) (Fin 2) F)
      (fun j => (a * b).right (v j)) =
    Matrix.mulVec (a.left : Matrix (Fin 2) (Fin 2) F)
      (fun j => a.right (semilinearApply b.left b.right v j))
  rw [hmap, Matrix.mulVec_mulVec]
  rfl

instance naturalAction : MulAction (Gamma F) (Fin 2 → F) where
  smul a v := semilinearApply a.left a.right v
  one_smul v := by
    change Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) F) v = v
    exact Matrix.one_mulVec v
  mul_smul a b v := semilinearApply_mul a b v


end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
