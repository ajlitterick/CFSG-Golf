module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphPoints
public import CFSG.Monster.B.TwoA.Amalgam.Deck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Geometry CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.CosetBuilding

theorem natCard_neighborSet_cv0_eq :
    Nat.card (cgraph.neighborSet cv0) = 3968055 := by
  rw [natCard_neighborSet_cv0]
  exact short_F4_deck_triviality_and_native_order.2.2.2.2.2.2.2.2.2


end CFSG.Monster.B.TwoA.Amalgam
