module

public import CFSG.Sporadic.FischerOddCore.Fi24WitCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi24WitCheck
public meta import Certificates.Certificate2078Base
public import Certificates.Kernel.Sporadic.Fi24OrbL.Facts
public meta import Certificates.Kernel.Sporadic.Fi24OrbL.Facts

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

@[expose] def fo24Packed (O : Enum) : Table :=
  Array.ofFn (n := nPts) fun i => O.par[i.1]! ||| (O.lab[i.1]! <<< 30)

@[expose] def fo24Gens (O : Enum) (l : Nat) : Table := if l = 1 then O.alpha else O.beta

@[expose] def fo24GensInv (O : Enum) (bInv : Table) (l : Nat) : Table :=
  if l = 1 then O.alpha else bInv

@[expose] def fo24ClsAt (O : Enum) (bInv pl tP : Table) (k : Nat) (q : Array Nat) : Array Nat :=
  applyTree pl (fo24Gens O) k (apT tP (applyTreeInv pl (fo24GensInv O bInv) k q))


end CFSG.Sporadic.FischerOddCore
