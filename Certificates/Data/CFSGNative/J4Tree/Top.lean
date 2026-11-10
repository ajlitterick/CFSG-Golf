module

public import Certificates.Data.CFSGNative.J4Tree.Inv
public import Certificates.Data.CFSGNative.J4Tree.Index
public import Std.Data.HashSet

public section

namespace CFSG.J4Tree.Native

open CFSG.ASVolI

set_option compiler.extract_closed false


inductive TopGen where
  | w (word : List Int)
  | c (c e : Nat)
deriving Inhabited


structure TopChild where
  y : Nat × Nat
  gensP : List (Nat × Nat)
  orbit : Nat
  orderP : Nat
  target : Nat
  conj : List Int
deriving Inhabited

structure TopNode where
  node : Nat
  N : Nat
  full : List TopGen
  two : List (Nat × Nat)
  orderTwo : Nat
  odd : List (Nat × List (List Int))
  ngens : List (List Int)
  children : List TopChild
  kids : List (Nat × Nat)
deriving Inhabited


@[noinline, expose] def topMergeOK (B0 : List Code) (B0s : Std.HashSet Code) (tb : List Code)
    (Sp : Std.HashSet Code) (h hi : Code) : Bool :=
  tb.all (fun b => B0s.contains (h * b * hi)) && B0.all fun r => Sp.contains (hi * r * h)


end CFSG.J4Tree.Native
