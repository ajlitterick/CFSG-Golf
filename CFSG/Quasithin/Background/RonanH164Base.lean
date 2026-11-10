module

public import CFSG.Quasithin.Background.RonanH163Base
public import CFSG.Quasithin.Background.RonanH143Hdata

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def c1 : List ℕ := [1]

@[expose] def c5 : List ℕ := [512, 256, 10, 6] ++ c1

@[expose] def c6 : List ℕ := 18 :: c5


@[expose] def V1 : Subgroup W10 := maskSub 10 c1

@[expose] def V5 : Subgroup W10 := maskSub 10 c5

@[expose] def V6 : Subgroup W10 := maskSub 10 c6


end CFSG.Quasithin.RonanH163
