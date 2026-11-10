module

public import Certificates.Data.CFSGNative.H13.LocDblDc
public import Certificates.Data.CFSGNative.Co2Rank.Dfs

public section

namespace CFSG.Quasithin.H13.LocDbl.DcRank

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Sporadic.Co2Rank

@[expose] def compT (t u : Array Nat) : Array Nat := u.map fun q => img t q

@[expose] def idT (n : Nat) : Array Nat := Array.range n


@[expose] def isInvT (n : Nat) (t : Array Nat) : Bool :=
  (compT t t == idT n) && (t != idT n)


end CFSG.Quasithin.H13.LocDbl.DcRank
