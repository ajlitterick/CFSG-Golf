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

@[expose] def T5 : Fin 2 → Fin 2 → Perm (Fin 6)
  | 0 => T5_0
  | 1 => T5_1


end CFSG.Quasithin.ShultG53
