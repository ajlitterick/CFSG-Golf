module

public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporCo3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native

@[expose] def pairText : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co3Schreier/co3-asch54-pair.txt"


@[expose] def pairAArrs : Array (Array Nat) :=
  Array.ofFn (n := 9) fun j => hexLine pairText.toUTF8 3 276 j.val

@[expose] def pairBArrs : Array (Array Nat) :=
  Array.ofFn (n := 10) fun j => hexLine pairText.toUTF8 3 276 (9 + j.val)


@[expose] def pairWordA0 : List Int :=
  [10, 15, 10, 7, -1, -3, 10, -1, 17, 5, 16, -9, 17, 5, 3, 2, -14, -4, -12, 17, 4, 2, 3, 2, -14,
    -4, -12, 17, 4, 2, 4, 4, 11, 2, 3, 2, -14, -4, -12, 17, 4, 2, 10, -17, -5, -10, 5, 17]

@[expose] def pairWordA1 : List Int :=
  [-17, -12, -2, -10, -2, -12, -2, -4, -17, 12, 4, 14, -2, -3, -2, -10, -2, -4, -17, 12, 4, 14, -2,
    -3, -2, -11, 3, 1, -10, -6, -5, -17, -10, -4, 17, -2, -17, -2, -16, -5, -17, 2, -10, 1, 17, 13,
    5, 2, 10]


end CFSG.LocalAnalysis.WeakClosure81.SporCo3
