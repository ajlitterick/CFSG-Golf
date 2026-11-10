module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

@[expose] def img (c i : Nat) : Nat := (c >>> (3 * i)) % 8

@[expose] def mulC (a b : Nat) : Nat :=
  img a (img b 0) + 8 * img a (img b 1) + 64 * img a (img b 2) + 512 * img a (img b 3) +
    4096 * img a (img b 4) + 32768 * img a (img b 5) + 262144 * img a (img b 6) +
    2097152 * img a (img b 7)

@[expose] def oneC : Nat := 16434824

@[expose] def validC (c : Nat) : Bool :=
  decide (c < 16777216) &&
    (List.range 8).all fun i => (List.range i).all fun j => img c i != img c j

@[expose] def invC (x : Nat) : Nat := Id.run do
  let mut y := x
  let mut k := 0
  while mulC y x != oneC && k < 40 do
    y := mulC y x
    k := k + 1
  return y


@[expose] def bfsChain (gens : List Nat) : List (Nat × Nat × Nat) := Id.run do
  let ga := gens.toArray
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert oneC
  let mut queue : Array Nat := #[oneC]
  let mut chain : Array (Nat × Nat × Nat) := #[]
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    for g in ga do
      let y := mulC x g
      if !seen.contains y then
        seen := seen.insert y
        queue := queue.push y
        chain := chain.push (y, x, g)
    i := i + 1
  return chain.toList


end CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
