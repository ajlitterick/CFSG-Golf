module

public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.AxisCount.BabySetup
public import CFSG.Monster.AxisCount.BabyCoverSpec

public section

namespace CFSG.Monster.Existence

theorem card_nativeB :
    Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder :=
  card_Cbar_eq_card_B.symm.trans AxisCount.Baby.natCard_Cbar_eq_monsterBabyOrder

end CFSG.Monster.Existence
