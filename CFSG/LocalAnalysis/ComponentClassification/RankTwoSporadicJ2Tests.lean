module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover

@[expose] def j2InP (t : Array ℕ) : Bool := inP t

@[expose] def j2InR (t : Array ℕ) : Bool := j2InP t || j2InP (compA 315 outerArr t)


@[expose] def j2PS : List ℕ := [0, 4, 3]

@[expose] def j2Fuel : ℕ := 2 ^ 20

theorem j2PS_lt : ∀ p ∈ j2PS, p < 315 := by decide


end CFSG.ComponentClassification.RankTwoSporadic.J2
