module

public import CFSG.Literature.ParrottTitsPresentation
public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsBasic
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Literature.ParrottTitsPresentation
public meta import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Literature.ParrottTits

open CFSG.CosetTable CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native


@[expose] def zword (w : List (Fin 10 × Bool)) : List ℤ :=
  w.map fun l => if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def parrottD0Word : List ℤ := [5, 4, 1, 2, 1, 2, 3, 9, 6, 9]

@[expose] def parrottD1Word : List ℤ := [10, 8, -7, 2, 1, 2, 1, 2, -9, 7, 8, 4]

end CFSG.Literature.ParrottTits
