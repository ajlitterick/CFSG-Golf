module

public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.CFSGNative.Co1.Involutions
public import Std.Data.HashSet
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Std.Data.HashSet

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.PtOrbit

open CFSG.Sporadic.Th.Native

structure PTree where
  pts : Array Nat
  par : Array Nat
  lab : Array Nat
deriving Inhabited


end CFSG.HardMathSupport.Solomon.Coordinator.PtOrbit
