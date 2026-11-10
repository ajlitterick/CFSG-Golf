module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] abbrev fStarMod (H : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)


end CFSG.Quasithin.RonanE42
