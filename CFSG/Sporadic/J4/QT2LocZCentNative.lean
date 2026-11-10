module

public import CFSG.Sporadic.J4.QT2LocX0Native
public import CFSG.Sporadic.J4.QTRankNative
public import Std.Data.HashSet.Basic

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def zcGenWords : List (List Int) :=
  [[-1, -2, -1, -2, -3, 1, 3, -2], [-1, -1, -2, -3, -3, -2, 3, 2],
    [-1, -2, 1, 3, 1, -2, 3, 3, 1]]

@[expose] def zcGenTabs : List (List Nat) := zcGenWords.map wordT


@[expose] def zcLocWf : Bool :=
  (locMats ()).size == 3 && (locInvs ()).size == 3 && (locMats ()).all wfRows &&
    (locInvs ()).all wfRows


end CFSG.Sporadic.J4.QT2
