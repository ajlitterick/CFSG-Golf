
module

public import CFSG.Monster.B.Rep4371.SmallFaithfulBase

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.OddDegree.Main
public import CFSG.Monster.B.Gen.GenerationBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Rep4371
open scoped Matrix

instance isSimpleGroup_Cbar :

    IsSimpleGroup Cbar := short_centralizer_generated_quotient_simple.2.2.1


end CFSG.Monster.B
