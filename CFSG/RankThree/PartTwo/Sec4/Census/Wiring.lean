module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Assembly4
public import CFSG.RankThree.PartOne.CTP.SpinRankFour
public import CFSG.RankThree.PartOne.CTP.BabyRankFour
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Item42

theorem rank3II_4_2 : Item4_2 :=
  rank3II_4_2_of_open PartOne.CTP.spinRankFour PartOne.CTP.rankFourBabyMonster
    PartTwo.Census.bridgeSp6Two PartTwo.Census.bridgeSp6Four PartTwo.Census.bridgeSp8Two
    PartTwo.Census.bridgeOmega8PlusTwo PartTwo.Census.bridgeOmega8MinusTwo
    spinLargePrimeRankThree

end Item42

section Item43


end Item43

section Item46


end Item46

section Census44


end Census44

section Item44


end Item44

end CFSG.RankThree.PartTwo.Sec4.Census
