module

public import CFSG.Milestones.ASVolI.B4Ext.SL3
public import CFSG.Milestones.ASVolI.B4Ext.ThreeT
public import CFSG.Milestones.ASVolI.B4Ext.WT
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

section ThreeMain

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(CFSG.Open.StatedSL 3 K) →* ↥G}


end ThreeMain

section ThreeFinal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end ThreeFinal

end CFSG.ASVolI
