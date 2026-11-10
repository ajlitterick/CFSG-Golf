module

public import CFSG.Milestones.ASVolI.B4Ext.StepN

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section BlocksD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {φ : Dual (ZMod 2) W} {w₀ : W}
  (hw₀ : φ w₀ = 1)


end BlocksD

section KEquivD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)


end KEquivD

section QStepD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)


end QStepD

section InductionD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

universe u


end InductionD

end CFSG.ASVolI
