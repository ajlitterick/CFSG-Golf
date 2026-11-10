module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog

@[expose] def witSylow : List (List ℕ) :=
  [[7], [2, 5, 7, 2, 7, 1, 2, 3, 7, 5, 6, 5, 7, 3, 1, 5, 1, 6],
    [4, 7, 4, 3, 7, 6, 2, 6, 7, 2, 7, 2, 3],
    [5, 7, 6, 7, 2, 6, 3, 7, 2, 7, 1, 5, 6, 1, 2, 1, 5, 1, 6],
    [1, 2, 7, 5, 7, 6, 3, 5, 6, 3, 6, 1, 2, 1]]

@[expose] def witConjB : List (List ℕ) :=
  [[2, 5, 1, 6, 3], [1, 5, 7, 4, 7, 2], [5, 6, 3, 6], [2, 3, 3, 3, 5, 4], [3, 5, 3, 4, 6, 2, 2],
    [6, 3, 5, 2]]

@[expose] def witConjAZ : List (List ℕ) :=
  [[5, 7, 4, 7, 2, 3], [6, 5, 4], [1, 6, 1, 2, 5, 6], [6, 4, 1, 3, 2, 1, 5], [6, 3, 5, 7, 2, 5],
    [4, 6, 5, 1, 7, 4], [3, 4, 5, 7, 5, 1, 2], [4, 7, 6, 5, 7, 3], [4, 3, 2, 5, 4, 5, 1],
    [1, 2, 3, 5]]


end CFSG.EvenSporadicStandard.HNRecog.CompatModel
