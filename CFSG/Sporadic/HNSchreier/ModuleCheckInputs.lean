module

public import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native


@[expose] def digitVec (s : String) : Array Nat :=
  (s.toList.map fun c => c.toNat - '0'.toNat).toArray

@[expose] def cRows (A B : Array (Array Nat)) : Array (Array Nat) :=
  let W1 := wordM (seedSel A B) [2, 1, 2, 1]
  let W2 := wordM (seedSel A B) [2, 1]
  let W4 := wordM (seedSel A B) [1, 2, 2, 1]
  let W5 := wordM (seedSel A B) [2, 2]
  Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j =>
    (W1[i]![j]! + 3 * W2[i]![j]! + 2 * B[i]![j]! + 4 * W4[i]![j]! + W5[i]![j]!) % 5

@[inline, expose] def skipOne (k : Nat) : Nat := if k < 1 then k else k + 1

@[expose] def minorRows (X : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 132) fun i => Array.ofFn (n := 132) fun j => X[skipOne i.val]![skipOne j.val]!

@[expose] def recVecs (w : Array Nat) (step : Nat → Array Nat → Array Nat)
    (recs : List (Nat × Nat)) : Array (Array Nat) :=
  (recs.drop 1).foldl (fun acc r => acc.push (step r.2 acc[r.1]!)) #[w]

@[expose] def recOK (w : Array Nat) (step : Nat → Array Nat → Array Nat) (recs : List (Nat × Nat))
    (vs : Array (Array Nat)) : Bool :=
  recs.length == 133 && vs.size == 133 && vs[0]! == w &&
    (List.range 133).all fun i => i == 0 || (decide (recs[i]!.1 < i) &&
      (recs[i]!.2 == 1 || recs[i]!.2 == 2) && vs[i]! == step recs[i]!.2 vs[recs[i]!.1]!)


end CFSG.Sporadic.HNSchreier.Native
