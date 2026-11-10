module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SylowCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.UMovWitness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzInputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.Suz


@[expose] def umovHex : String := include_str "SuzUMoves.txt"

@[expose] def umovTbl (k : ℕ) : Table := hexT 3 1782 (1782 * k) umovHex


end CFSG.EvenSporadicStandard.Solomon78
