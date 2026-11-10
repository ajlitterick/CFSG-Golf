module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPair
public import Certificates.Data.CFSGNative.F4.T46Simple
public import Certificates.Data.CFSGNative.McL.Certificate

public section

namespace CFSG.Monster.Existence.CoPair.Native

open CFSG.Sporadic.Th.Native (ap)
open CFSG.F4.Native (t46XT t46YT)

set_option compiler.extract_closed false

@[expose] def seedW1 (_ : Unit := ()) : Nat := 1

@[expose] def seedW2 (_ : Unit := ()) : Nat := 4096


@[expose] def u62WordA (_ : Unit := ()) : List Nat :=
  [1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1]

@[expose] def u62WordB (_ : Unit := ()) : List Nat :=
  [0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0]


@[expose] def mclWordA (_ : Unit := ()) : List Nat :=
  [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]

@[expose] def mclWordB (_ : Unit := ()) : List Nat :=
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0,
    1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0]


end CFSG.Monster.Existence.CoPair.Native
