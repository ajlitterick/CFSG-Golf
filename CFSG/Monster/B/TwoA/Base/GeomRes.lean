
module

public import CFSG.Monster.B.TwoA.Base.GeomResBase

public import CFSG.Monster.B.TwoA.Base.GeomObj
public import CFSG.Monster.B.TwoA.Base.PetersenC
public import CFSG.Monster.B.Cbar.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

attribute [local instance] parAction


instance isSimpleGroup_Shat :
    IsSimpleGroup Shat :=
  have : IsSimpleGroup Cbar := short_centralizer_generated_quotient_simple.2.2.1
  (MonoidHom.ofInjective iotaD_injective).symm.isSimpleGroup


end CFSG.Monster.B.TwoA
