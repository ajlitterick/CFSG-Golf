module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix


abbrev tMat : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 0], !![1, 1, 0; 1, 1, 0; 0, 0, 0]]


end CFSG.Quasithin.RonanH49
