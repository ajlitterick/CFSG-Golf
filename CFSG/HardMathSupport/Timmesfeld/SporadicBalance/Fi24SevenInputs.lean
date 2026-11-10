module

public import Certificates.Data.CFSGNative.Fi24.Certificate
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByTree
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByTree
public import CFSG.Foundations.Basic
public meta import CFSG.Foundations.Basic
public import CFSG.Perm.ChainByOrder
public meta import CFSG.Perm.ChainByOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

structure RepData where
  rep : Nat
  chain : Array Nat
  cent : Array Nat
  omega : List Nat
  e : Nat
  m : Nat
  wit : Array (List Nat)

structure Data where
  words : Array (List Int)
  ix : Nat
  iy : Nat
  ic : Nat
  conj : Array (Nat × List Nat)
  repA : RepData
  repB : RepData

@[expose] def parseLists (s : String) : Array (List Nat) :=
  (s.splitOn ";").toArray.map fun t => if t.isEmpty then [] else (t.splitOn ",").map String.toNat!

@[expose] def parseInt (t : String) : Int :=
  if t.startsWith "-" then -Int.ofNat (t.drop 1).toNat! else Int.ofNat t.toNat!

@[expose] def parseIntLists (s : String) : Array (List Int) :=
  (s.splitOn ";").toArray.map fun t => if t.isEmpty then [] else (t.splitOn ",").map parseInt

@[expose] def parsePairs (s : String) : Array (Nat × List Nat) :=
  (s.splitOn ";").toArray.map fun t =>
    match t.splitOn "|" with
    | [a, b] => (a.toNat!, if b.isEmpty then [] else (b.splitOn ",").map String.toNat!)
    | _ => (0, [])

@[expose] def subLetters (L : Array Table) (ws : Array Nat) : Array Table :=
  Array.ofFn (n := 2 * ws.size) fun i =>
    if i.val % 2 = 0 then L[2 * ws[i.val / 2]!]! else L[2 * ws[i.val / 2]! + 1]!


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
