module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native

@[expose] def kSpec : List (List (ℕ × ℕ)) :=
  [[(1, 1)],
    [(2, 1), (1, 1), (2, 7)],
    [(2, 2)]]


@[expose] def nSpecK : List (List (ℕ × ℕ)) :=
  [[(1, 2), (2, 2), (3, 3)],
    [(2, 5), (2, 1), (3, 2)],
    [(1, 4), (3, 1), (2, 4)],
    [(1, 1), (3, 3), (2, 4), (1, 3)],
    [(1, 1), (2, 2), (3, 3), (1, 1), (3, 2)],
    [(1, 1), (2, 5), (1, 5), (3, 3), (2, 3)]]

@[expose] def xSpecK : List (ℕ × ℕ) :=
  [(5, 1), (4, 1), (6, 1), (3, 1), (1, 1)]

@[expose] def ySpecK : List (ℕ × ℕ) :=
  [(2, 1)]

@[expose] def qSpecK : List (List (ℕ × ℕ)) :=
  [[(1, 1), (4, 1)],
    [(5, 1), (2, 1)],
    [(3, 1), (2, 1), (1, 1)],
    [(1, 1)]]

@[expose] def cSpecK : List (ℕ × ℕ) :=
  [(5, 1), (1, 1), (5, 1), (1, 1)]

@[expose] def eSpecK : List (List (ℕ × ℕ)) :=
  [[(4, 1), (2, 1), (1, 1), (4, 1), (3, 1)],
    [(5, 1), (2, 1)],
    [(5, 1), (1, 1), (5, 1), (1, 1)]]

@[expose] def kWords : List (List ℕ) := kSpec.map (specWord classz.centGens)


@[expose] def nWordsK : List (List ℕ) := nSpecK.map (specWord kWords)

@[expose] def xWordK : List ℕ := specWord nWordsK xSpecK
@[expose] def yWordK : List ℕ := specWord nWordsK ySpecK

@[expose] def zcWordsK : List (List ℕ) := [xWordK, yWordK]

@[expose] def qWordsK : List (List ℕ) := qSpecK.map (specWord nWordsK)

@[expose] def cWordK : List ℕ := specWord nWordsK cSpecK

@[expose] def eWordsK : List (List ℕ) := eSpecK.map (specWord nWordsK)

end CFSG.EvenSporadicStandard.HNRecog
