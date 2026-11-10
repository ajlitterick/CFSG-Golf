module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuData
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.RuSchreier

@[expose] def ruInP (t : Array ℕ) : Bool :=
  siftA 4060 (rawLevels 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase))
    (ruBaseArr 4060 ruJoinBase) 0 t


@[expose] def ruPS : List ℕ := [0, 1, 2, 3]


theorem ruPS_lt : ∀ p ∈ ruPS, p < 4060 := by decide

@[expose] def ruE0 : Array (Array ℕ) := #[ruA0A, ruHexRow ruE0RText.toUTF8 4060 0]


end CFSG.ComponentClassification.RankTwoSporadic.Ru
