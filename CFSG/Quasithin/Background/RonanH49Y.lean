module

public import CFSG.Quasithin.Background.RonanH49YMat
public import CFSG.Quasithin.Background.HL3WrWreath

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix IsMulCommutative


abbrev Tw (i : Fin 3) : WMod := Multiplicative.ofAdd (tMat i)


end CFSG.Quasithin.RonanH49
