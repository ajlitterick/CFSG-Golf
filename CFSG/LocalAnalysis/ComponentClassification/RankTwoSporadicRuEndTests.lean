module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Fischer

@[expose] def ruEndB0 : Array ℕ := ruHexRow ruEndText.toUTF8 4060 0

@[expose] def ruEndLeaves : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun i => ruHexRow ruEndText.toUTF8 4060 (i.val + 1)

@[expose] def ruEndN0 : Array (Array ℕ) :=
  Array.ofFn (n := 2) fun i => ruHexRow ruEndText.toUTF8 4060 (i.val + 9)


end CFSG.ComponentClassification.RankTwoSporadic.Ru
