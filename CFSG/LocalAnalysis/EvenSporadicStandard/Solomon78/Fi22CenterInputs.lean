module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SylowCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.UMovWitness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.Fi22


@[expose] def fi22UmovHex : String := include_str "Fi22UMoves.txt"


end CFSG.EvenSporadicStandard.Solomon78
