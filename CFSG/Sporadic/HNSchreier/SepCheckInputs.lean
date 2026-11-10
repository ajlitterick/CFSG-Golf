module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native

@[expose] def rowsM : Array (Array Nat) := rowsOf 5 133 Data.formPayload

@[expose] def formChecks (A B M : Array (Array Nat)) : Bool :=
  colsMat 133 M == M && mulM 5 133 M (invM 5 133 M) == idM 133 &&
    mulM 5 133 (mulM 5 133 (colsMat 133 A) M) A == M &&
    mulM 5 133 (mulM 5 133 (colsMat 133 B) M) B == M


end CFSG.Sporadic.HNSchreier.Native
