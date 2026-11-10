module

public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.Sporadic.Schreier.PairJ3Check
public meta import CFSG.Sporadic.SmallOddCore.J3Data
public meta import CFSG.Sporadic.Schreier.PairJ3Check

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2.Native

@[expose] def j3PGTbls : Array Table :=
  #[j3StrongArrs[0]!.map UInt32.ofNat, j3StrongArrs[1]!.map UInt32.ofNat]


@[expose] def j3Sift (T : Table) : Bool := siftA 6156 PairJ3.levels PairJ3.baseArr 0 (natArr T)


end CFSG.Sporadic.SmallOddCore
