module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native

@[expose] def mulTree (n : Nat) (gens : Array (Array Nat)) (par lab : Array Nat) :
    Array (Array Nat) :=
  (List.range (par.size - 1)).foldl
    (fun E i => E.push (compA n gens[lab[i + 1]!]! E[par[i + 1]!]!)) #[idA n]


end CFSG.Sporadic.FischerOddCore

end
