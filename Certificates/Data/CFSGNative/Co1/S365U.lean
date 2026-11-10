module

public import Certificates.Data.CFSGNative.Co1.Odd
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Co1.S365UNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

@[expose] def onePlus (Mt : Array Nat) (p : Nat) : Nat := p ^^^ vecMulN 24 Mt p

@[expose] def reduceBy (basis : List (Nat × Nat)) (u q : Nat) : Nat × Nat :=
  basis.foldl (fun acc b => if acc.1.testBit b.1.log2 then (acc.1 ^^^ b.1, acc.2 ^^^ b.2) else acc)
    (u, q)

@[expose] def insertBasis (basis : List (Nat × Nat)) (u q : Nat) : List (Nat × Nat) :=
  let r := reduceBy basis u q
  if r.1 == 0 then basis
  else
    let hi := basis.filter fun b => r.1.log2 < b.1.log2
    let lo := basis.filter fun b => !decide (r.1.log2 < b.1.log2)
    hi ++ (r :: lo)

@[expose] def imBasis (Mt : Array Nat) : List (Nat × Nat) :=
  (List.range 24).foldl (fun basis j => insertBasis basis (onePlus Mt (1 <<< j)) (1 <<< j)) []

@[expose] def memPre (basis : List (Nat × Nat)) (u : Nat) : Option Nat :=
  let r := reduceBy basis u 0
  if r.1 == 0 then some r.2 else none

@[expose] def witness (Qt pts : Array Nat) (pos : Array UInt32) (n : Nat) (Rt St Tt : Array Nat) :
    Option (Nat × Nat × Nat × Nat) :=
  let bR := imBasis Rt
  let bS := imBasis St
  let bT := imBasis Tt
  (List.range (2 ^ bR.length - 1)).findSome? fun m =>
    let mask := m + 1
    let w := (List.range bR.length).foldl
      (fun acc i => if mask.testBit i then (acc.1 ^^^ bR[i]!.1, acc.2 ^^^ bR[i]!.2) else acc)
      (0, 0)
    if type4N Qt pts pos n w.1 then
      match memPre bS w.1, memPre bT w.1 with
      | some p2, some p3 => some (w.1, w.2, p2, p3)
      | _, _ => none
    else none


end CFSG.Sporadic.Co1.S365UNative
