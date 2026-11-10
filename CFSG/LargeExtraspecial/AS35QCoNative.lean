module

public import Std.Data.HashSet.Basic

public section

namespace CFSG.LargeExtraspecial.AS35QCo.Native

@[expose] def ofBitsN (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0

@[expose] def ent (c i j : Nat) : Bool := c.testBit (6 * i + j)

@[expose] def dotc (c d i k : Nat) : Bool :=
  (List.range 6).foldl (fun acc j => acc ^^ (ent c i j && ent d j k)) false

@[expose] def mulc (c d : Nat) : Nat := ofBitsN 36 fun p => dotc c d (p / 6) (p % 6)

@[expose] def transc (c : Nat) : Nat := ofBitsN 36 fun p => ent c (p % 6) (p / 6)

@[expose] def idc : Nat := 34630287489

@[expose] def jc : Nat := 4328915976

@[expose] def isSp (c : Nat) : Bool := mulc (mulc (transc c) jc) c == jc


@[expose] def repc : Nat → Nat
  | 0 => 4565631105
  | 1 => 1343258784
  | 2 => 1343652000
  | _ => 1108378656


@[expose] def witc : Nat × Nat := (2410230404, 11669084179)

@[expose] def bigOrder (x : Nat) : Bool :=
  !(x == idc) && !(mulc x x == idc) && !(mulc (mulc x x) x == idc) &&
    !(mulc (mulc x x) (mulc x x) == idc)

@[expose] def prodOK (k : Nat) : Bool :=
  isSp witc.1 && mulc witc.1 witc.2 == idc && mulc witc.2 witc.1 == idc &&
    bigOrder (mulc (repc k) (mulc (mulc witc.1 (repc k)) witc.2))


end CFSG.LargeExtraspecial.AS35QCo.Native
