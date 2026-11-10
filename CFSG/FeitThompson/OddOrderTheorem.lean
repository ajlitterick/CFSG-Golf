module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.FeitThompson

theorem isSolvable_of_odd_natCard (G : Type*) [Group G] [Finite G] (hG : Odd (Nat.card G)) :
    Group.IsSolvable G :=
  CFSG.odd_order_theorem G hG

end CFSG.FeitThompson
