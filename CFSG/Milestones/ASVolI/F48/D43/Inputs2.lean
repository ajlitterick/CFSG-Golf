module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false


abbrev burnsideF48d_xyW : List (Fin 17 × Bool) := [((0 : Fin 17), true), ((1 : Fin 17), true)]

abbrev burnsideF48d_w0W : List (Fin 17 × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true)]

abbrev burnsideF48d_W1 : List (Fin 17 × Bool) :=
  [(5, true)] ++ burnsideF48d_w0W ++ [(5, true)] ++
    [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false)] ++ [(5, true), (0, false)]

abbrev burnsideF48d_W2 : List (Fin 17 × Bool) :=
  [(5, true), (0, true), (1, true), (0, true), (12, true), (0, false), (1, false), (0, false),
    (5, true), (0, false)]


end CFSG.ASVolI
