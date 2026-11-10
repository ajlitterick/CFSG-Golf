module

public import CFSG.YGroups.DCE.B433Y333
public import CFSG.YGroups.DCE.FixUpper
public import CFSG.YGroups.DCE.FixForest
public import CFSG.YGroups.DCE.SiftChain

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] def dWord : Array ℕ := #[0, 1, 2, 3, 8, 9, 5]

@[expose] noncomputable def dY : YGroup 4 3 2 := evalWord (yGen 4 3 2) dWord.toList ^ 9

@[expose] def dArr (L : Array ByteArray) : ByteArray :=
  (List.range 9).foldl (fun acc _ => bcomp 31671 acc (wordB L dWord)) (bid 31671)


@[expose] noncomputable def tau (W : Array (Array ℕ)) (ω : ℕ) : YGroup 4 3 2 :=
  evalWord (yGen 4 3 2) W[ω]!.toList


@[expose] def dConj (L : Array ByteArray) (W : Array (Array ℕ)) (ω : ℕ) : ByteArray :=
  bcomp 31671 (bcomp 31671 (wordB L W[ω]!) (dArr L)) (binvCand 31671 (wordB L W[ω]!))


@[expose] def fixCount (L : Array ByteArray) (W : Array (Array ℕ)) (G : Array ByteArray)
    (levels : Array (ℕ × Array ByteArray)) : Option ℕ :=
  let f := forestRec 31671 G
  let pass : Array Bool := (Array.range 31671).map fun r =>
    f.2.2.2[r]! == r && siftB 31671 levels (dConj L W r)
  if forestValid 31671 G f && allLt 31671 (fun r => f.2.2.2[r]! != r ||
      bisInv 31671 (wordB L W[r]!) (binvCand 31671 (wordB L W[r]!))) then
    some ((List.range 31671).foldl (fun a w => if pass[f.2.2.2[w]!]! then a + 1 else a) 0)
  else none


section Node


end Node


end CFSG.YGroups.DCE.B433
