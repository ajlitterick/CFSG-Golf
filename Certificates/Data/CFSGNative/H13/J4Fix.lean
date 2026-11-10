module

public import Certificates.Data.CFSGNative.H13.J4Elems

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.J4.Native


@[expose] def tInvRows (_ : Unit := ()) : Array V2 := (tOf (uvPairsOf basePairs)).2

end CFSG.Quasithin.H13.J4.Native
