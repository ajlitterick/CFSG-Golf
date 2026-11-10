module

public import CFSG.CGT.Stroth77.Section224CExtension

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}


theorem type200_rhoM_mulVec (Q : Fin 3 → ℤ) :
    Type200.ρM *ᵥ Q = ![Q 0 - Q 2, -Q 2, Q 1 - Q 2] := by
  funext i
  fin_cases i <;>
    simp [Type200.ρM, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring


end CFSG.CGT.Stroth77

end
