module

public import CFSG.ClassicalInvolution.Q3.TL3Main
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement


theorem sl2Three_exists_order_three : ∃ y : SL(2, ZMod 3), y ^ 3 = 1 ∧ y ≠ 1 := by
  decide +kernel

theorem sl2Three_centralizer_card :
    ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → y ≠ 1 →
      Fintype.card {z : SL(2, ZMod 3) // z * y = y * z} ≤ 6 := by
  decide +kernel


end CFSG.ClassicalInvolution.Q3
