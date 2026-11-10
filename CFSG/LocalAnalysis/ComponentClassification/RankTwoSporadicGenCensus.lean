module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {gens : Array (Array ℕ)}
  {ps : List ℕ} {fuel : ℕ} {prog : List (ℕ × ℕ)} {d : CensusData} {allowU : Bool} {k m : ℕ}


theorem yCensus_top_le_top {W : Type*} [Group W] :
    YCensus (⊤ : Subgroup W) (· ≤ (⊤ : Subgroup W)) :=
  fun _ _ _ h => absurd le_top h

end CFSG.ComponentClassification.RankTwoSporadic.Cert
