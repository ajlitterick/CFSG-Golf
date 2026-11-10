module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def l34GensR : Array (Array ℕ) := CFSG.PSL3Four.Native.gTabs

@[expose] def l34GensS : Array (Array ℕ) := CFSG.PSL3Four.Native.gensS

@[expose] def l34PS : List ℕ := [0, 1, 5, 10, 3]


theorem l34PS_lt : ∀ p ∈ l34PS, p < 42 := by decide


end CFSG.ComponentClassification.RankTwoL3Four.HypII
