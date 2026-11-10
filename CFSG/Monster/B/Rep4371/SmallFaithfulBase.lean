
module

public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Assembly.LowTwoRankDefs

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Rep4371
open scoped Matrix


@[expose] noncomputable def matR :
    Module.End ℚ Vst ≃ₐ[ℚ] Matrix (Fin 4371) (Fin 4371) ℚ :=
  LinearMap.toMatrixAlgEquiv Rbasis


end CFSG.Monster.B
