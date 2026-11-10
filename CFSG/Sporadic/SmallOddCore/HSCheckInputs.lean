module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.Schreier.PairHSCheck
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.Schreier.PairHSCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Co2.Native

@[expose] def hsPGTbls : Array Table :=
  #[hsStrongArrs[0]!.map UInt32.ofNat, hsStrongArrs[1]!.map UInt32.ofNat]

@[expose] def hsPGInvTbls : Array Table := hsPGTbls.map (invT 3850)

@[expose] def hsSift (T : Table) : Bool :=
  siftA 3850 PairHS.levels PairHS.baseArr 0 (natArr T)


end CFSG.Sporadic.SmallOddCore
