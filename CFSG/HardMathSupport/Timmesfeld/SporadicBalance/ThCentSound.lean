
module


public import CFSG.Sporadic.Th.Certificate
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1
public import CFSG.Sporadic.Th.CertificateBase1

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

theorem rowsMatrix_seedA : rowsMatrix (rowsOf seedA) = matJ a := by
  rw [rowsMatrix_rowsOf_seedA, matJ, a_val]

theorem rowsMatrix_ab (w : List ℤ) :
    rowsMatrix (wordRows (rowsOf seedA) (rowsOf seedB) w) = matJ (wordG (pairLetters a b) w) :=
  rowsMatrix_wordRows rowsMatrix_seedA rowsMatrix_seedB a_sq_kernel b_cube_kernel w


theorem rowsMatrix_xRows : rowsMatrix (xRows ()) = matJ xJ := rowsMatrix_ab xWord

theorem rowsMatrix_yRows : rowsMatrix (yRows ()) = matJ yJ := rowsMatrix_ab yWord


section Facts


end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
