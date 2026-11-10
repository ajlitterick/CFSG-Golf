module

public import Certificates.Data.CFSGNative.CTIB.Lift

public section

namespace CFSG.Monster.B.CTIB.Native

open CFSG.Monster.B.Max2.Native

set_option compiler.extract_closed false

@[expose] def censusAct (k v : Nat) : Nat := act22 (if k = 0 then r1Rows else r2Rows) v

@[expose] def censusRecs (_ : Unit := ()) : List (Nat × Nat) :=
  [(1, 2300), (3, 46575), (7, 2049300), (17, 1619200), (19, 476928)]


@[expose] def squaresOK (_ : Unit) : Bool :=
  qmul gArr 1 1 == 0 && qmul gArr 3 3 == 0 && qmul gArr 7 7 == 0 &&
    qmul gArr 17 17 == 2 ^ 22 && qmul gArr 19 19 == 2 ^ 22

end CFSG.Monster.B.CTIB.Native
