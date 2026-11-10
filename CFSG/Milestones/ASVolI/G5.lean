module

public import CFSG.Quasithin.Background.RonanG52Main
public import CFSG.Quasithin.Background.RonanG51F4
public import CFSG.Quasithin.Background.ShultG53Final

public section

namespace CFSG.ASVolI.ChG

open CFSG.QuasithinUnique

structure FMod (X : Type) [Group X] where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module (ZMod 2) carrier]
  [finite : Finite carrier]
  ρ : Representation (ZMod 2) X carrier

attribute [instance] FMod.addCommGroup FMod.module FMod.finite

namespace FMod

variable {X : Type} [Group X]


end FMod


section Perm

open Classical

variable {X : Type} [Group X]


end Perm

section Rad

variable {X A : Type} [AddCommGroup A] (act : X → A → A)


end Rad

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.ASVolI.ChG CFSG.ASVolI.ChG.FMod CFSG.QuasithinUnique


section G51Cert

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Quasithin.H13.A6 (g5G1 cA6)


end G51Cert


section G52Cert


end G52Cert


section G53Cert

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


end G53Cert

end CFSG.ASVolI
