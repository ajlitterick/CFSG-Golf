module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SylowCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.UMovWitness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.Fi22


@[expose] def fi22UmovHex : String := include_str "Fi22UMoves.txt"

@[expose] def fi22UmovTbl (k : ℕ) : Table := hexT 3 3510 (3510 * k) fi22UmovHex

@[expose] def fi22UmovData : Bool :=
  (List.range 3).all fun i => (List.range 6).all fun j =>
    umovWitOK 3510 siftP (fi22UmovTbl (6 * i + j)) (tT i) (tT j)

end CFSG.EvenSporadicStandard.Solomon78
