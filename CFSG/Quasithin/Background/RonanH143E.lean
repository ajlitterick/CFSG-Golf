module

public import CFSG.Quasithin.Background.RonanH143PG
public import CFSG.Quasithin.Background.RonanH143Data2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.QuasithinUnique.Setup.X1

@[expose] def PG.all : List PG :=
  (List.finRange 16).flatMap fun t => (List.finRange 8).map fun j => ⟨t, j⟩


end CFSG.Quasithin.RonanH143
