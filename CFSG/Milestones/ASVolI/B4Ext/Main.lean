module

public import CFSG.Milestones.ASVolI.B4Ext.StepD
public import CFSG.Milestones.ASVolI.B4Ext.Base
public import CFSG.Milestones.ASVolI.B4Ext.Four

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section H1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end H1

section Translate

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


end Translate

section Part2iF1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin


end Part2iF1

end CFSG.ASVolI
