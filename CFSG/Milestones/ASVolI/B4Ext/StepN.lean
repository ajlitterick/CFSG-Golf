module

public import CFSG.Milestones.ASVolI.B4Ext.Inv
public import CFSG.Milestones.ASVolI.B4Ext.Defs

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section BlocksN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {φ : Dual (ZMod 2) W} {w₀ : W}
  (hw₀ : φ w₀ = 1)


end BlocksN

section KEquivN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)


end KEquivN

section QStepN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)


end QStepN

section InductionN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

universe u


end InductionN

end CFSG.ASVolI
