module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.KD.Co1K105

open CFSG.Sporadic.SmallF2.Native

@[expose] def t24Codes : List (Nat × Nat) :=
  [(145, 19049461067090809466252873200666015961935189),
   (125, 30186669490188212324833515829496339306),
   (123, 4541745440266336267019832564003460459),
   (113, 8877899011685098669842919838112437)]

@[expose] def wordOf (len code : Nat) : List Bool := (List.range len).map fun k => code.testBit k

@[expose] def mulM (M N : Array Nat) : Array Nat := mulRows 11 N M

@[expose] def wordM (cA cB : Array Nat) (w : List Bool) : Array Nat :=
  w.foldl (fun acc c => mulM acc (if c then cB else cA)) (idRows 11)

@[expose] def gensOf (Aa Ba : Array Nat) (codes : List (Nat × Nat)) : Array (Array Nat) :=
  let cA := transposeRows 11 Aa
  let cB := transposeRows 11 Ba
  (codes.map fun c => wordM cA cB (wordOf c.1 c.2)).toArray


end CFSG.KD.Co1K105
