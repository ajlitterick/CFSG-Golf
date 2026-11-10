module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.SuzOddCore

@[expose] def suzInM (t : Array ℕ) : Bool := siftA 1782 smallLevels smallBaseNat.toArray 0 t

@[expose] def suzInT (t : Array ℕ) : Bool := suzInM t || suzInM (compA 1782 vArr t)


@[expose] def suzPS : List ℕ := [0, 1, 2, 3, 4, 8]


theorem suzPS_lt : ∀ p ∈ suzPS, p < 1782 := by decide

@[expose] def suzE0 : Array (Array ℕ) :=
  #[hexTable 3 1782 0 suzE0Text, hexTable 3 1782 1782 suzE0Text]


end CFSG.ComponentClassification.RankTwoSporadic.Suz
