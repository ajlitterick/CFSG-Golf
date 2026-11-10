
module

public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def fi22N0List : List ℕ :=
  (List.range 3510).filter fun i => i != 0 && ((fi22OuterStrong3510 1)[0]!)[i]! == i

@[expose] def fi22Nbr : Array (List ℕ) := adjSearch 3510 fi22OrigArrs fi22N0List


end CFSG.Monster.B.Fischer
