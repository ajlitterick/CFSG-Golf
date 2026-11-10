module

public import Std.Data.HashSet

public section

set_option compiler.extract_closed false

namespace CFSG.PrimeSteinNative

@[expose] def allLtGo (n : Nat) (f : Nat → Bool) (i : Nat) : Bool :=
  if i < n then (if f i then allLtGo n f (i + 1) else false) else true
termination_by n - i

@[expose] def allLt (n : Nat) (f : Nat → Bool) : Bool := allLtGo n f 0


@[expose] def reflAux (p bi : Nat) (b row : List Nat) : List Nat :=
  List.zipWith (fun bj cj => (bj + cj * bi) % p) b row

@[expose] def reflL (p : Nat) (rows : List (List Nat)) (i : Nat) (b : List Nat) : List Nat :=
  reflAux p (b.getD i 0) b (rows.getD i [])

@[expose] def actL (p : Nat) (rows : List (List Nat)) (word : List Nat) (b : List Nat) :
    List Nat :=
  word.foldr (reflL p rows) b


structure RTab where
  vecs : Array (List Int)
  hts : Array Int
  imgs : Array (Array Nat)

@[expose] def dotL (a b : List Int) : Int := (List.zipWith (· * ·) a b).sum


@[expose] def hsL (T : RTab) (t : List Nat) : List Int := t.map fun k => T.hts.getD k 0


end CFSG.PrimeSteinNative
