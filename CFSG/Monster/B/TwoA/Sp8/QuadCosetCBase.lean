
module

public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase
public meta import CFSG.Monster.B.TwoA.Sp8.QuadDataBase
public meta import CFSG.Monster.B.TwoA.Sp8.QuadInvBase
public meta import CFSG.Monster.B.TwoA.Sp8.ElemAbBase
public meta import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetCInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

theorem qPoly_zero' : qPoly 0 = 0 := by decide

theorem cImg_triality : cImg 44 = 0 := by decide

end CFSG.Monster.B.TwoA.Sp8
