module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co3

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def co3InP (t : Array ℕ) : Bool :=
  siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 t


@[expose] def co3PS : List ℕ := [0, 1, 2, 3, 4, 5, 6]


theorem co3PS_lt : ∀ p ∈ co3PS, p < 276 := by decide


end CFSG.ComponentClassification.RankTwoSporadic.Co3
