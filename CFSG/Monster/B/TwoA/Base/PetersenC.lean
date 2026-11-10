
module

public import CFSG.Monster.B.TwoA.Base.PetersenCBase

public import CFSG.Monster.B.TwoA.Base.PetersenA

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise


instance finite_X4 :
    Finite X4 := Nat.finite_of_card_ne_zero (by rw [natCard_X4]; decide)

instance finite_X5 :
    Finite X5 := Nat.finite_of_card_ne_zero (by rw [natCard_X5]; decide)


end CFSG.Monster.B.TwoA
