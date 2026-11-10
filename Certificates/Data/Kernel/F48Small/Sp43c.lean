module

public import Certificates.Data.Kernel.F48Small.Pack

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] def decSp43c (i : Nat) : Char :=
  ['a', 'b', 'c', 'p', 'q', 'A', 'B', 'C', 'P', 'Q'].getD i 'a'


end CFSG.KC.F48S
