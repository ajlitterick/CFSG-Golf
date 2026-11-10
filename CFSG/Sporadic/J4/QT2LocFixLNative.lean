module

public import CFSG.Sporadic.J4.QT2LocCntNative
public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def rep5Vec : V2 := pathVec (repPaths.getD 5 [])

@[expose] def orb5 : VOrb := vorbit locTabs rep5Vec 15180 15

@[expose] def fixedIn (M : Array V2) (O : VOrb) : List V2 :=
  let T := frTable M
  (O.pts.filter fun v => (frApply T v).beq v).toList


end CFSG.Sporadic.J4.QT2
