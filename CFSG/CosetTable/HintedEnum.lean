module

public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.CosetTable


@[expose] def Params.restrict (P : Params) (idx : List Nat) : Params :=
  if idx.isEmpty then P
  else { P with scans :=
    (mkParams P.L P.inv (idx.map fun i => (P.rels.getD i ([], [])).1) []).scans }

structure Block where
  path : List Nat
  rels : List (List Nat)
  lim : Nat
  scan : List Nat


end CFSG.CosetTable
