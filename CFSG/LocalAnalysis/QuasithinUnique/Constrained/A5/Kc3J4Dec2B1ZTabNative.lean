module

public import CFSG.Sporadic.J4.QT2ANative
public import CFSG.Sporadic.J4.QTRankNative

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A


@[expose] def zTabOK (M Mi : Array V2) (T : List Nat) : Bool :=
  lenOK T && (List.range 11).all fun j =>
    eqRows (mulRows (mulRows M (etaE (2 ^ j))) Mi) (etaE (T.getD j 0))

end CFSG.QuasithinUnique.A5
