module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J3

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native


@[expose] def j3UArr : Array ℕ :=
  CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.j3OuterTbl


@[expose] def j3PS : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7]


theorem j3PS_lt : ∀ p ∈ j3PS, p < 6156 := by decide


end CFSG.ComponentClassification.RankTwoSporadic.J3
