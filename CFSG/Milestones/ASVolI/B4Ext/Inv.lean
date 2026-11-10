module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section Inv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]


end Inv

section Vanish

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end Vanish

end CFSG.ASVolI
