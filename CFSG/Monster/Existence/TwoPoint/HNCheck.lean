module

public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.TwoPoint.HNData
public import Certificates.Data.CFSGNative.Bridge.HNGPL

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

@[expose] def hnLetterW (l : ℕ × Bool) : List Native.Gen :=
  if l.2 then hnWU[l.1]! else hnWV[l.1]!

@[expose] def hnRelW (R : List (ℕ × Bool)) : List Native.Gen :=
  (R.reverse.map hnLetterW).flatten


@[expose] def hnWAB : List Native.Gen := hnWBeta ++ hnWAlpha

@[expose] def hnWAB5 : List Native.Gen := hnWAB ++ hnWAB ++ hnWAB ++ hnWAB ++ hnWAB


end CFSG.Monster.Existence
