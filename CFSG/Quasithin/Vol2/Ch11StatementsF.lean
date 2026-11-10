module

public import CFSG.Quasithin.Vol2.Ch11StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section Defs

variable {G : Type} [Group G]


abbrev bOf (T I H : Subgroup G) : Subgroup G :=
  fsuV T I ⊓ Subgroup.centralizer (VZ T H : Set G)

abbrev pOf (T I H : Subgroup G) (h : G) : Subgroup G :=
  bOf T I H ⊔ conjSubgroup (bOf T I H) h


end Defs


end CFSG.Quasithin.Vol2.Ch11
