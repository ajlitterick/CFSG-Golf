module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi22

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer

@[expose] def hypHex : String := include_str "Fi22Hyp.txt"

@[expose] def hypTbl (j : ℕ) : Table := hexT 3 3510 (3510 * j) hypHex

@[expose] def tT (k : ℕ) : Table := (fi22ExtArr (21 + k)).map UInt32.ofNat

@[expose] def uT : Table := fi22GraphOuterArr.map UInt32.ofNat

@[expose] def siftP (T : Table) : Bool := fi22InP (natArr T)


@[expose] def memP (t T : Table) : Bool := siftP T && commTT 3510 T t


@[expose] def zT : ℕ → Table
  | 0 => hypTbl 3
  | 1 => hypTbl 10
  | _ => hypTbl 18


@[expose] def lT (k : ℕ) : Table := hypTbl (40 + k)


@[expose] def zData : Bool :=
  zOK 3510 siftP uT (tT 0) (zT 0) && zOK 3510 siftP uT (tT 1) (zT 1) &&
    zOK 3510 siftP uT (tT 2) (zT 2) && zOK 3510 siftP uT (tT 3) (tT 3) &&
    zOK 3510 siftP uT (tT 4) (tT 4) && zOK 3510 siftP uT (tT 5) (tT 5)


end CFSG.EvenSporadicStandard.HypOne.Fi22
