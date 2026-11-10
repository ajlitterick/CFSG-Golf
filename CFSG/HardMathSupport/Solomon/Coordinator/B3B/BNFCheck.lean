module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.BCheck
public import Certificates.Data.CFSGNative.MonsterB.BinaryRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

set_option compiler.extract_closed false

@[expose] def bG (k : Nat) : Nat := [81, 60].getD k 0


@[expose] def nfXData : List (List Nat) :=
  [[2, 2, 2, 2, 0, 0, 2, 2, 2], [2, 0, 2, 0, 2, 2, 2, 2, 2], [0, 1, 0, 1, 2, 1, 0, 1, 2],
   [2, 2, 1, 2, 1, 1, 0, 1, 0],
   [1, 1, 0, 2, 0, 0, 2, 0, 0], [2, 0, 2, 2, 1, 2, 0, 2, 0], [1, 1, 1, 0, 0, 2, 0, 0, 0],
   [1, 0, 1, 0, 1, 2, 0, 1, 1]]

@[expose] def nfYData : List (List Nat) :=
  [[1, 2, 1, 0, 0, 0, 1, 1, 1], [0, 1, 0, 0, 0, 2, 2, 2, 2], [2, 1, 0, 2, 0, 0, 2, 0, 0],
   [0, 2, 0, 2, 0, 2, 1, 2, 2],
   [1, 0, 0, 1, 2, 1, 0, 1, 0], [2, 2, 1, 1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0],
   [2, 0, 0, 0, 1, 2, 0, 0, 1]]


end CFSG.HardMathSupport.Solomon.Coordinator.B3B
