module

public import CFSG.Sporadic.Presentation.Co2CoverInputs

public section

namespace CFSG.Sporadic.Presentation.Co2

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration


abbrev gW : List (Fin gc × Bool) := [(gb, true), (gb, true)]

abbrev conjW (i : Fin 4) : List (Fin gc × Bool) :=
  FreeGroup.invRev gW ++ substWord hs (dW.getD i []) ++ gW ++
    FreeGroup.invRev (substWord hs (dpW.getD i []))


end CFSG.Sporadic.Presentation.Co2
