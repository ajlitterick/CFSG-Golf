module

public import CFSG.Sporadic.Co2Schreier.Arrays
public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import Std.Data.HashMap

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporCo2

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.Schreier.Co3.Native

@[expose] def pairText : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co2Schreier/co2-asch54-pair.txt"


@[expose] def pairWordA0 : List Int := [2, 5, -1, 7, -6, -19, -7]

@[expose] def pairWordA1 : List Int :=
  [7, 7, 19, 6, -7, -24, -21, 8, 4, 10, 22, 7, 5, 10, 16, 8, 7, 24, 8, 22, 16, 21, 8, -5, 13, 19,
    -2, 21, 2, 17, 1, 5, 18, 29, 11, 3, 21, 11, 8, 24, 7, 4, -21, 10, 7, 8, 22, 7, 5, 10, -2, 13,
    -2, 21, 2, 4, 25, 15, 13, 29, 26, 22, 25, 12, 1, 12, 6, 9, 8, 24, 7, 4, -21, 10, 7, 8, 22, 7, 5,
    10, -2, 13, -2, 21, 2, 4, 25, 15, 13, 29, 26, 22, 25, 12, 24, 7, -8, 22, 3, 11, 3, 21, 11, -21,
    10, 7, 8, 22, 7, 6, 2, 13, 17, 6, 7, 19, 21, 14, 16, 13, 18, 28, 2, 23, 11, 4, 3, 2, 19, 6, -7,
    1, 6, 11, 4, 12, 1, 8, 24, 7, 4, -21, 10, 7, 8, 22, 7, 5, 10, -2, 13, -2, 21, 2, 4, 25, 15, 13,
    29, 26, 22, 25, 12, -8, 18, -24, -21, 8, 4, 10, 22, 7, 6, 10, 22, 7, 5, -13, -8, -21, 22]


end CFSG.LocalAnalysis.WeakClosure81.SporCo2
