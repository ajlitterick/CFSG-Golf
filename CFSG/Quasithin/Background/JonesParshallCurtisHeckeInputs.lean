module

public import CFSG.Quasithin.Background.JonesParshallCurtisGroupInputs
public import CFSG.Quasithin.Background.JonesParshallCurtisWeylInputs

public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

@[expose] def rootB : Bool × Fin 4 → BM
  | (true, s) => xB s
  | (false, s) => yB s

@[expose] def rootBM (l : List (Bool × Fin 4)) : BM := l.foldr (fun a M => bmul (rootB a) M) bone


end CFSG.Quasithin.JonesParshall.Curtis
