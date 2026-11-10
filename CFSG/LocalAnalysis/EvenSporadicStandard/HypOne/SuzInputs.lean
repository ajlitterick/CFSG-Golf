module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Suz

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore

@[expose] def hypHex : String := include_str "SuzHyp.txt"

@[expose] def hypTbl (k : ℕ) : Table := hexT 3 1782 (1782 * k) hypHex


@[expose] def siftM (T : Table) : Bool := inM (natArr T)


end CFSG.EvenSporadicStandard.HypOne.Suz
