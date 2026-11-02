module

public import CFSG.Monster.GMS.S4FamilyTwoB
public import CFSG.Monster.GMS.S4FamilyAssemble
public import CFSG.Monster.GMS.S4FamilyAdjust

public section

namespace CFSG.Monster.GMS.S4Family

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4Family
