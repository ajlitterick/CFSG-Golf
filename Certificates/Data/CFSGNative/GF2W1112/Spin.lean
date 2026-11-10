module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native


@[expose] def w12Dot (d x y : Nat) : Bool :=
  (List.range d).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) false


@[expose] def w12QN (d : Nat) (qt : Array Nat) (x : Nat) : Bool := w12Dot d x (vecMulN d qt x)

@[expose] def w12BN (d : Nat) (ft : Array Nat) (x y : Nat) : Bool := w12Dot d x (vecMulN d ft y)


end CFSG.GF2W1112
