module

public import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22QG (c k : Nat) : Array Nat := fi22CentArr (fi22CentStrongStart.getD c 0 + k)

@[expose] def fi22QGi (c k : Nat) : Array Nat := invCand 3510 (fi22QG c k)

@[expose] def fi22QArr (c : Nat) (seed : Array Nat) (steps : List (Nat × Nat)) :
    Array (Array Nat) :=
  steps.foldl (fun Q st => Q.push (conjArr 3510 (fi22QG c st.1) (fi22QGi c st.1) Q[st.2]!)) #[seed]


@[expose] def fi22QTwoArr : Array (Array Nat) :=
  fi22QArr 2 (Native.powA 3510 (compA 3510 (fi22QG 2 0) (fi22QG 2 1)) 10)
    [(2, 0), (0, 1), (1, 1), (2, 2), (0, 3)]

@[expose] def fi22QZeroArr : Array (Array Nat) :=
  fi22QArr 0 (Native.powA 3510 (compA 3510 (fi22QG 0 0) (fi22QG 0 5)) 4)
    [(1, 0), (2, 0), (3, 0), (4, 0), (6, 0), (8, 0), (9, 0), (11, 0)]

end CFSG.Sporadic.FischerOddCore
