module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndData
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Fischer

@[expose] def suzEndB0 : Array ℕ := hexTable 3 1782 0 suzEndText

@[expose] def suzEndLeaves : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun i => hexTable 3 1782 (1782 * (i.val + 1)) suzEndText

@[expose] def suzEndL : Array (Array ℕ) :=
  Array.ofFn (n := 2) fun i => hexTable 3 1782 (1782 * (i.val + 9)) suzEndText

@[expose] def suzEndSigma : Array ℕ := hexTable 3 1782 (1782 * 11) suzEndText

@[expose] def suzEndC0 : Array ℕ := hexTable 3 1782 (1782 * 12) suzEndText


end CFSG.ComponentClassification.RankTwoSporadic.Suz
