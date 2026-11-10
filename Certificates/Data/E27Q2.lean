module

public import Certificates.Data.E27Fus
public import Certificates.Data.CFSGNative.He.Fp

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.He.Native


structure S0Data where
  n : Nat
  h : Nat
  m : Nat
  gensStr : String
  parStr : String
  LStr : String
  ksStr : String
  bsStr : String
  g3 : Nat × Nat × Nat := (0, 0, 0)

namespace S0Data

@[expose] def parseNats (s : String) : Array Nat :=
  (((s.replace "\n" " ").splitOn " ").filter fun t => !t.isEmpty).toArray.map String.toNat!


@[expose, reducible] def d (D : S0Data) : Nat := D.h + D.h


@[expose] def L (D : S0Data) : Array (Array Nat) :=
  let a := parseNats D.LStr
  Array.ofFn (n := D.m) fun j => Array.ofFn (n := D.n) fun i => a[j.val * D.n + i.val]!


end S0Data

end CFSG.HardMathSupport.Foote.E27

end
