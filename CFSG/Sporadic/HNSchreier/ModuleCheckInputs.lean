module

public import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native


@[expose] def recOK (w : Array Nat) (step : Nat → Array Nat → Array Nat) (recs : List (Nat × Nat))
    (vs : Array (Array Nat)) : Bool :=
  recs.length == 133 && vs.size == 133 && vs[0]! == w &&
    (List.range 133).all fun i => i == 0 || (decide (recs[i]!.1 < i) &&
      (recs[i]!.2 == 1 || recs[i]!.2 == 2) && vs[i]! == step recs[i]!.2 vs[recs[i]!.1]!)


end CFSG.Sporadic.HNSchreier.Native
