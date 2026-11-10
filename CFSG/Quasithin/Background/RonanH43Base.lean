module

public import CFSG.Quasithin.Background.HSL3One

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

abbrev PV : Type := PairMod (ZMod 2)

abbrev mk (v w : Fin 3 → ZMod 2) : PV := (Multiplicative.ofAdd v, Multiplicative.ofAdd w)


end CFSG.Quasithin.RonanH43
