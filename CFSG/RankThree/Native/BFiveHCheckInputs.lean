module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public meta import Certificates.Data.CFSGNative.MonsterB.Primes

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

@[expose] def bFiveHRows : List (List Nat) :=
  [[0, 1, 0, 0], [3, 1, 1, 0], [2, 2, 2, 0], [1, 1, 1, 4]]

@[expose] def bFiveHC : List Nat := [0, 1, 2, 2]


end CFSG.RankThree.Native
