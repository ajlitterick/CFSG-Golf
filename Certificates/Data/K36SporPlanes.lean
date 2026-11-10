module

public import Certificates.Data.CoreD2Lines

public section

namespace Certificates.K36Spor

open CFSG.PSL3Four.Native Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

structure Cent where
  idx : Nat
  f1 : Nat
  f2 : Nat
deriving Inhabited

structure Exc where
  idx : Nat
  cW : List (List Int)
  cc : List Cent
  yW : List Int
  fWc : List (List Int)
  fyWc : List (List Int)
  wA : List Int
  wB : List Int
deriving Inhabited

structure SData where
  base : Data
  ys : List Nat
  gc : List Cent
  gen : List Nat
  wAs : List (List Int)
  wBs : List (List Int)
  exc : List Exc
  kCap : Nat
deriving Inhabited


@[expose] def allowedS (S : SData) (i j : Nat) : Bool :=
  let c := S.gc.getD j default
  c.idx == i || c.f2 == 0


@[expose] def cT (S : SData) (X : Exc) : Array Tab := (X.cW.map (wT S.base)).toArray

@[expose] def cTi (S : SData) (X : Exc) : Array Tab := (cT S X).map (invTab S.base.n)


end Certificates.K36Spor
