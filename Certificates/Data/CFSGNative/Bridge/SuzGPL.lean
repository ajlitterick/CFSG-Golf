module

public import Certificates.Data.CFSGNative.Suz.Certificate

public section

namespace CFSG.Sporadic.Bridge.SuzGPL.Native

open CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def rels (_ : Unit := ()) : List (List (Nat × Bool)) := [
    [(0, true), (0, true)],
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(4, true), (4, true)],
    [(5, true), (5, true)],
    [(6, true), (6, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true)],
    [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
    [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true),
      (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
    [(1, true), (5, true), (1, true), (5, true), (1, true), (5, true)],
    [(5, true), (6, true), (5, true), (6, true), (5, true), (6, true), (5, true), (6, true)],
    [(6, true), (1, true), (6, true), (1, true), (6, true), (1, true)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, true), (3, true), (0, true), (3, true)],
    [(0, true), (4, true), (0, true), (4, true)],
    [(0, true), (5, true), (0, true), (5, true)],
    [(0, true), (6, true), (0, true), (6, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(1, true), (4, true), (1, true), (4, true)],
    [(2, true), (4, true), (2, true), (4, true)],
    [(2, true), (5, true), (2, true), (5, true)],
    [(2, true), (6, true), (2, true), (6, true)],
    [(3, true), (5, true), (3, true), (5, true)],
    [(3, true), (6, true), (3, true), (6, true)],
    [(4, true), (5, true), (4, true), (5, true)],
    [(4, true), (6, true), (4, true), (6, true)],
    [(0, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true),
      (3, true)],
    [(0, false), (5, true), (6, true), (5, true), (6, true)],
    [(0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true),
      (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true),
      (0, true), (1, true), (2, true), (5, true)],
    [(1, true), (5, true), (6, true), (1, true), (5, true), (6, true), (1, true), (5, true),
      (6, true), (1, true), (5, true), (6, true), (1, true), (5, true), (6, true)],
    [(1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true),
      (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true),
      (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true),
      (3, true), (4, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true),
      (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true),
      (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true),
      (3, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (2, true),
      (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true),
      (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true),
      (1, true), (2, true), (3, true), (2, true), (3, true), (4, true)],
    [(0, true), (1, true), (2, true), (6, true), (0, true), (1, true), (2, true), (6, true),
      (0, true), (1, true), (2, true), (6, true), (0, true), (1, true), (2, true), (6, true),
      (0, true), (1, true), (2, true), (6, true)]]

@[expose] def imgText : String := include_str "SuzGPLImages.txt"

@[expose] def surjText : String := include_str "SuzGPLSurj.txt"

@[expose] def parseLine (s : String) : List Int :=
  (s.splitOn " ").filterMap String.toInt?

@[expose] def parseWords (s : String) : Array (List Int) :=
  (((s.splitOn "\n").filter fun l => !l.isEmpty).map parseLine).toArray

@[expose] def imgWords (_ : Unit := ()) : Array (List Int) := parseWords imgText

@[expose] def surjWords (_ : Unit := ()) : Array (List Int) := parseWords surjText

@[expose] def relLetter (l : Nat × Bool) : Int :=
  if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

@[expose] def imgLetter (I Iv : Array Table) (z : Int) : Table :=
  if 0 < z then I[(z - 1).toNat]! else Iv[(-z - 1).toNat]!

@[expose] def seedLetter (G4 : Array Table) (z : Int) : Table :=
  if z = 1 then G4[0]! else if z = -1 then G4[1]! else if z = 2 then G4[2]! else G4[3]!


end CFSG.Sporadic.Bridge.SuzGPL.Native
