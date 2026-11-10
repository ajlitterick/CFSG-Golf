module

public import Certificates.Data.CFSGNative.GF2W1112.Spin

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native

@[expose] def w12UEqR (X Y : Array Nat) : Bool :=
  (List.range 22).all fun i => (X[i]?.getD 0) % 2 ^ 22 == (Y[i]?.getD 0) % 2 ^ 22


end CFSG.GF2W1112
