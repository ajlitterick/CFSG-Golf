module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native

set_option compiler.extract_closed false

@[expose] def frG1 : List Nat :=
  [25, 16, 25, 17, 13, 14, 24, 12, 16, 11, 20, 13, 10, 9, 4, 17, 6, 12, 8, 0, 22, 0, 19]

@[expose] def frH0 : List Nat :=
  [19, 21, 19, 14, 13, 14, 18, 23, 15, 23, 8, 10, 18, 11, 8, 22, 6, 6, 20, 7, 25, 0, 9, 17, 20]

@[expose] def frWc0 : List Nat := [21, 16, 8, 1]

@[expose] def frWc1 : List Nat := [20, 13, 1]

@[expose] def frEps : List (List Nat) := [
  [24, 19, 21, 19, 15, 24, 17, 13, 14, 14, 10, 21, 14, 20, 13],
  [25, 23, 17, 25, 12, 14, 16, 24, 14, 10, 15, 25, 12, 20],
  [16, 21, 18, 20, 12, 15, 19, 20, 15, 18, 10, 10, 19, 20, 14],
  [24, 17, 24, 15, 23, 19, 14, 22, 9, 9, 18, 15, 18],
  [25, 20, 19, 12, 14, 14, 14, 23, 13, 19, 8, 12, 17, 10, 24],
  [24, 20, 22, 20, 12, 17, 13, 14, 24, 17, 8, 8, 16, 18, 25]]


@[expose] def frPt (c : Ctx) (w : List Nat) : Nat := ap (wordTab c w) 0


@[expose] def frLam (c : Ctx) (c0 c1 : Nat) : List Nat :=
  [0, 305530, clsPt c 0 305530, c0, c1, clsPt c c0 c1]


end CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native
