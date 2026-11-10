module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1Full
public import CFSG.Sporadic.Schreier.J1CertData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J1

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def j1Gens : Array (Array ℕ) :=
  #[CFSG.Sporadic.Schreier.j1A1List.toArray, CFSG.Sporadic.Schreier.j1A2List.toArray]

@[expose] def j1PS : List ℕ := [0, 1, 2]


theorem j1PS_lt : ∀ p ∈ j1PS, p < 3080 := by decide


end CFSG.ComponentClassification.RankTwoSporadic.J1
