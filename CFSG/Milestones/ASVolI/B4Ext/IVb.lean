module

public import CFSG.Milestones.ASVolI.B4Ext.IVa
public import CFSG.Milestones.ASVolI.B4Ext.Main
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Milestones.ASVolI.B4Ext.Psi

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section IVb

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Type} [Field K]
  [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL 5 K) →* ↥G}


end IVb

section PreW

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)


end PreW

section IVc

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end IVc

end CFSG.ASVolI
