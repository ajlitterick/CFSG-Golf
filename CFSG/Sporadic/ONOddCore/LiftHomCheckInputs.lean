module

public import CFSG.Sporadic.ONOddCore.LiftCheck
public meta import CFSG.Sporadic.ONOddCore.LiftCheck

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native

@[expose] def liftArrs (hA : Array (Array Nat)) (e : LiftEntry) : Array (Array Nat) :=
  (e.words.map (posArr nPts hA)).toArray


end CFSG.Sporadic.ONOddCore
