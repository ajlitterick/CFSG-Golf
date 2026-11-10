module

public import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.Co3Arrays
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def co3IndexNineYList : List Nat :=
  [28, 43, 55, 141, 144, 158, 168, 173, 232, 242, 253, 269]


@[expose] def co3IndexNineXWord : List Nat := [9, 7, 13, 7, 10, 13, 5, 4, 10]

@[expose] def co3IndexNineYWord : List Nat := [8, 12, 14, 14, 6, 9, 13, 5]


end CFSG.Sporadic.Schreier.Co3
