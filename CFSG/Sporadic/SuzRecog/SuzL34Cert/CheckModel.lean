module

public import CFSG.Sporadic.SuzRecog.C1ModelTests

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

abbrev Dec := List Nat × Nat

@[expose] def s1pDecs : List Dec :=
  [([4, 9, 8, 1, 3, 1], 20), ([6, 8, 1, 2, 6, 1], 42), ([3, 1, 2, 1, 3], 0), ([], 56)]

@[expose] def l1Decs : List Dec :=
  [([], 1), ([], 10), ([], 93), ([8, 9, 8, 9, 4], 99)]

@[expose] def m1Decs : List Dec :=
  [([5, 3, 8, 9, 3, 1], 50), ([], 53), ([], 64), ([], 23), ([9, 4, 6, 4, 2], 73),
    ([4, 3, 9, 5, 6, 1], 106), ([8, 9, 8, 9, 4], 105), ([9, 8, 2, 9, 4], 77)]

@[expose] def cl1Decs : List Dec :=
  [([6, 5, 9, 8, 3, 2], 4), ([3, 7, 8, 5], 72), ([5, 8, 9, 7, 4, 5], 22),
    ([2, 9, 7, 9, 7, 2], 31)]

@[expose] def nl1Decs : List Dec :=
  [([2, 7, 1, 5, 2], 66), ([1, 9, 5, 3, 7], 84)]

@[expose] def m21Decs : List Dec :=
  [([], 86), ([], 1), ([8], 110), ([8], 0)]

@[expose] def l1CompDecs : List Dec :=
  [([8], 0), ([8], 110)]

@[expose] def tauDec : Dec := ([6, 7, 8, 4], 78)

@[expose] def lam0Dec : Dec := ([9, 7, 5, 2, 7, 3], 4)

@[expose] def aDec : Dec := ([7, 8, 5, 3], 95)

@[expose] def ntl1Decs : List Dec :=
  [([8], 110), ([8], 0), ([7, 8, 5, 3], 2), ([], 1), ([4, 3, 9, 5, 6, 1], 106), ([], 87),
    ([8, 1, 2, 1], 34), ([9, 8, 2, 9, 4], 71)]

@[expose] def tbarTabs : Array Tab :=
  #[#[0, 1, 5, 4, 3, 2, 6, 7, 9, 8, 12, 13, 10, 11, 15, 14],
    #[0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]]

@[expose] def xA : Tab := #[0, 1, 3, 2, 5, 4, 6, 7, 14, 15, 13, 12, 11, 10, 8, 9]

@[expose] def xBs : Array Tab :=
  #[#[0, 8, 7, 15, 10, 2, 13, 5, 9, 1, 14, 6, 3, 11, 4, 12],
    #[0, 8, 5, 13, 15, 7, 10, 2, 9, 1, 12, 4, 6, 14, 3, 11],
    #[0, 8, 15, 7, 3, 11, 12, 4, 9, 1, 6, 14, 10, 2, 5, 13],
    #[0, 8, 12, 4, 7, 15, 11, 3, 9, 1, 5, 13, 14, 6, 2, 10]]

@[expose] def decs (l : List Dec) : Array Tab := (l.map decTab).toArray

@[expose] def bitProd (B : Array Tab) (i : Nat) : Tab :=
  (List.range B.size).foldl (fun r k => if i.testBit k then comp 1782 r B[k]! else r) (idTab 1782)

@[expose] def l1Tabs (_ : Unit := ()) : Array Tab :=
  let B := decs l1Decs
  Array.ofFn (n := 16) fun i => bitProd B i.val

@[expose] def m21Tabs (_ : Unit := ()) : Array Tab :=
  let B := decs m21Decs
  Array.ofFn (n := 16) fun i => bitProd B i.val


end CFSG.Sporadic.SuzRecog.SuzL34Cert
