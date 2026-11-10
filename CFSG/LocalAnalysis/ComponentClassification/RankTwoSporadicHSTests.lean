module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HS

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def hsInP (t : Array ℕ) : Bool :=
  siftA 100 (rawLevels 100 hs100StrongArrs hs100BaseArr) hs100BaseArr 0 t


@[expose] def hsPS : List ℕ := [0, 1, 2, 3, 4]


theorem hsPS_lt : ∀ p ∈ hsPS, p < 100 := by decide


end CFSG.ComponentClassification.RankTwoSporadic.HS
