module

public import CFSG.Quasithin.Background.ShultG53Main
public import CFSG.Quasithin.Background.ShultG53Part5Pack

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv


instance (k : Fin 2) (y : V4) : Decidable (linePred k y) :=
  match k with
  | 0 => inferInstanceAs (Decidable (predLine4a y))
  | 1 => inferInstanceAs (Decidable (predLine4b y))


end CFSG.Quasithin.ShultG53
