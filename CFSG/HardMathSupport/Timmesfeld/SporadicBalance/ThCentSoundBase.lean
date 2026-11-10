
module

public import Certificates.Data.CFSGNative.Timmesfeld.ThCent
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Th.ChainBase

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

theorem wordG_cons {G : Type*} [Group G] (gens : ℤ → G) (l : ℤ) (w : List ℤ) :
    wordG gens (l :: w) = gens l * wordG gens w := by
  simp only [wordG, List.map_cons, List.prod_cons]

theorem rowsMatrix_powRowsN (M : Array V4) (e : ℕ) :
    rowsMatrix (powRowsN M e) = rowsMatrix M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact rowsMatrix_idRows
  | succ e ih => rw [powRowsN, rowsMatrix_mulRows, ih, pow_succ]


section Facts


end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
