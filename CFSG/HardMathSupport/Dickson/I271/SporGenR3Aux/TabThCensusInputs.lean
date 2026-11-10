module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalCheck
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalCheck
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalData
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public meta import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabThNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

set_option compiler.extract_closed false

@[expose] def progU : List Op := [
  .mul 0 1 2, .mul 2 1 3, .pow 4 2 4, .mul 4 1 5, .mul 5 3 6, .mul 3 3 7, .mul 7 7 8, .mul 4 7 9,
  .mul 8 9 10, .pow 3 8 11, .mul 11 4 12, .mul 10 11 13, .pow 18 13 14, .mul 14 0 15, .mul 15 13 16,
  .pow 19 12 17, .mul 17 6 18, .mul 18 12 19, .mul 16 19 20, .mul 19 16 21, .pow 10 20 22
  ]


open CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
  CFSG.Monster.B.Fischer CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal


end CFSG.HardMathSupport.Dickson.I271.TabThNative
