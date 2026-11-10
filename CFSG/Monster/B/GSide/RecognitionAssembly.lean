module

public import CFSG.Monster.B.GSide.Setup
public import CFSG.Sporadic.B

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB

noncomputable def shatEquivB :
    Shat ≃* Blueprint.NativeSporadic.B :=
  (iotaEquiv.trans sEquiv).symm

theorem isSimpleGroup_Shat :
    IsSimpleGroup Shat := by
  have := CFSG.Sporadic.B.fam_b_simplicity
  with_reducible_and_instances exact MulEquiv.isSimpleGroup shatEquivB


end CFSG.Monster.B.GSide
