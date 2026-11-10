module

public import Certificates.Data.CoreD2Perm

public section

namespace Certificates.CoreD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

structure GKind where
  kind : Nat
  idx : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
deriving Inhabited

structure VData where
  base : Data
  ys : List Nat
  gk : List GKind
  wAs : List (List Int)
  wBs : List (List Int)
deriving Inhabited


@[expose] def allowed (V : VData) (i j : Nat) : Bool :=
  let f := V.gk.getD j default
  f.kind == 0 || f.idx == i || f.f2 == 0

@[expose] def wordOK (V : VData) (i : Nat) (w : List Int) : Bool :=
  w.all fun l => allowed V i (l.natAbs - 1)


end Certificates.CoreD2Perm
