module

public import CFSG.Sporadic.Schreier.Co1LocalModule
public import CFSG.Sporadic.Schreier.Co1LocalEnd

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix WeightProj

theorem z_ne_one :
    ThreeLocal.z ≠ 1 := by
  intro h
  apply zM_mulVec_ne_self (q_ne_zero 0)
  change ((ThreeLocal.z : GL24) : Mat24) *ᵥ q 0 = q 0
  rw [h, Units.val_one, one_mulVec]


end CFSG.Sporadic.Co1Schreier
