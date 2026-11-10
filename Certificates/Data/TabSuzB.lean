module

public import Certificates.Data.TabSuzFuse
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzBKit
public meta import Certificates.Data.TabSuzFuse
public meta import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzBKit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabSuzB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse

@[expose] def aTuples : Array (Array Nat) :=
  #[#[1742, 1132, 1303, 181, 761, 1286], #[1422, 818, 409, 1226, 422, 1270],
    #[654, 857, 989, 491, 1111, 149], #[1, 2, 0, 1531, 1225, 1526]]

@[expose] def aKeys : List Nat := [3]


@[expose] def aGens (_ : Unit := ()) : Array (Array Nat) :=
  let L := levels ()
  aTuples.map (rebuild L)


end CFSG.HardMathSupport.Dickson.I271.TabSuzB
