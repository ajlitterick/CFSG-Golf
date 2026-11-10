module

public import CFSG.Milestones.ASVolI.H1

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V]


theorem map_zpowers (g : MulAut V) (v : V) :
    (Subgroup.zpowers v).map (g : MulAut V).toMonoidHom = Subgroup.zpowers (g v) :=
  MonoidHom.map_zpowers (g : MulAut V).toMonoidHom v


end CFSG.ASVolI.ChH
