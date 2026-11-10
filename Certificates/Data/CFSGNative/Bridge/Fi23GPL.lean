module

public import Certificates.Data.CFSGNative.Fi23.Certificate

public section

namespace CFSG.Sporadic.Bridge.Fi23GPL.Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def powWord (w : List (Nat × Bool)) (n : Nat) : List (Nat × Bool) :=
  (List.replicate n w).flatten

@[expose] def rels (_ : Unit := ()) : List (List (Nat × Bool)) :=
  let squareWords := (List.range 10).map fun k => [(k, true), (k, true)]
  let edgePairs : List (Nat × Nat) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)]
  let edgeWords := edgePairs.map fun (r, s) => powWord [(r, true), (s, true)] 3
  let nonedgePairs : List (Nat × Nat) :=
    [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9),
      (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9),
      (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9),
      (3, 5), (3, 6), (3, 8), (3, 9),
      (4, 6), (4, 7), (4, 8), (4, 9),
      (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (7, 9), (8, 9)]
  let nonedgeWords := nonedgePairs.map fun (r, s) => powWord [(r, true), (s, true)] 2
  squareWords ++ edgeWords ++ nonedgeWords ++
    [powWord [(3, true), (2, true), (1, true), (3, true), (4, true), (5, true),
        (3, true), (7, true), (8, true)] 10,
      powWord [(0, true), (1, true), (2, true), (3, true), (4, true), (5, true),
        (7, true)] 9]

@[expose] def imgText : String := include_str "Fi23GPLImages.txt"

@[expose] def surjText : String := include_str "Fi23GPLSurj.txt"

@[expose] def parseLine (s : String) : List Int :=
  (s.splitOn " ").filterMap String.toInt?

@[expose] def parseWords (s : String) : Array (List Int) :=
  (((s.splitOn "\n").filter fun l => !l.isEmpty).map parseLine).toArray

@[expose] def imgWords (_ : Unit := ()) : Array (List Int) := parseWords imgText

@[expose] def surjWords (_ : Unit := ()) : Array (List Int) := parseWords surjText


@[expose] def imgLetter (I Iv : Array Table) (z : Int) : Table :=
  if 0 < z then I[(z - 1).toNat]! else Iv[(-z - 1).toNat]!

@[expose] def seedLetter (G4 : Array Table) (z : Int) : Table :=
  if z = 1 then G4[0]! else if z = -1 then G4[1]! else if z = 2 then G4[2]! else G4[3]!


end CFSG.Sporadic.Bridge.Fi23GPL.Native
