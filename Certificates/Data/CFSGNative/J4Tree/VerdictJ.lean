module

public import Certificates.Data.CFSGNative.J4.F2
public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Index

public section

namespace CFSG.J4Tree.VerdictJ

open CFSG.Sporadic.J4.Native

set_option compiler.extract_closed false


@[expose] def w5 (s : String) : List Int :=
  s.toList.filterMap fun ch =>
    if 'a' ≤ ch ∧ ch ≤ 'e' then some ((ch.toNat - 'a'.toNat + 1 : Nat) : Int)
    else if 'A' ≤ ch ∧ ch ≤ 'E' then some (-((ch.toNat - 'A'.toNat + 1 : Nat) : Int))
    else none

structure Ctx where
  lT : Array (Array V2)
  lTi : Array (Array V2)
  cT : Array (Array V2)
  cTi : Array (Array V2)
  idT : Array V2
  uM : Array (Array V2)
  kM : Array (Array V2)
  fM : Array (Array V2)


structure NPData where
  node : Nat
  g : List (String × List Int)
  V : List (Nat × Nat)
  masks : List Nat

structure FData where
  node : Nat
  d : List (String × List Int)
  masks : List Nat


end CFSG.J4Tree.VerdictJ
