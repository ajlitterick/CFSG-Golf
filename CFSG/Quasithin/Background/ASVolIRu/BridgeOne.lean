module

public import CFSG.Milestones.ASVolI.J1
public import CFSG.Quasithin.Recognition.RuTypeSetting
public import CFSG.Quasithin.Background.ASVolIRu.StUniqueDefs
public import CFSG.Quasithin.Vol2.Ch10SecAElemAb
public import CFSG.Open.StatedZModTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK.RuType

namespace BridgeOne

open CFSG.Open CFSG.Open.StatedAPI
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem centerOf_eq (W : Subgroup G) : centerOf W = CFSG.Quasithin.centerOf W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨w, hw⟩
    simpa using congrArg Subtype.val this
  · rintro ⟨hxW, hxc⟩
    refine ⟨⟨x, hxW⟩, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc w w.2)


section FromRuType


end FromRuType

section Abstract


end Abstract

section Steinberg


end Steinberg

end BridgeOne

open CFSG.Open


end CFSG.ASVolI.ChIJK.RuType
