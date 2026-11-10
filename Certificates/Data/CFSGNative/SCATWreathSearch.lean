module

public import Certificates.Data.CFSGNative.SCATWreathCode

public section

namespace CFSG.SCATWreath

structure GD where
  n : Nat
  mul : Nat → Nat → Nat
  gens : Array Nat
  ginv : Array Nat
  ord : Array Nat
  inv : Array Nat
  dom : List Nat
  lab : Array Nat
  reps : Array Nat
  wit : Array Nat
  csz : Array Nat


@[expose] def GD.conj (D : GD) (d u : Nat) : Nat := D.mul (D.mul d u) D.inv[d]!


end CFSG.SCATWreath
