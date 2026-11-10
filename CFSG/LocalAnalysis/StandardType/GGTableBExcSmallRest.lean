module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBExcSmallRest

@[expose] def GGTableBExcSmallRestLabel (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der


section Labels


theorem largeEvenLabelAll_card_lt_smallRest (h3 : GGTriD4ThreeRankInput)
    (hF : GGTwF4RankInput) (hT : GGTitsThreeRankInput) {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (h : GGTableBExcSmallRestLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  rcases h with ht | ht | ht | ht
  · exact largeEvenLabelAll_card_lt_triD4 (fun _ => h3) hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_twF4 hF hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_G2der hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_twF4der hT hp hlab ht hs


end Labels

end TableBExcSmallRest

section Inputs


theorem ggBstarInputOn_smallRest (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput) :
    GGBstarInputOn TableBExcSmallRest.GGTableBExcSmallRestLabel :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_smallRest h3 hF hT hp hlab h hs

theorem ggStdSubPreInputOn_smallRest (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput) :
    GGStdSubPreInputOn TableBExcSmallRest.GGTableBExcSmallRestLabel :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_smallRest h3 hF hT hp hlab h hs


end Inputs

@[expose] def GGTableBOtherRestNoSmall (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRest4NoF4 p lab ∧ ¬ TableBExcSmallRest.GGTableBExcSmallRestLabel p lab


section RoundFour


theorem ggBstarInputOn_rest4NoF4_of_noSmall (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput)
    (h : GGBstarInputOn GGTableBOtherRestNoSmall) : GGBstarInputOn GGTableBOtherRest4NoF4 :=
  ((ggBstarInputOn_smallRest h3 hF hT).or h).mono fun p lab _ _ hl => by
    by_cases hS : TableBExcSmallRest.GGTableBExcSmallRestLabel p lab
    exacts [Or.inl hS, Or.inr ⟨hl, hS⟩]

theorem ggStdSubPreInputOn_rest4NoF4_of_noSmall (h3 : TableBExcSmallRest.GGTriD4ThreeRankInput)
    (hF : TableBExcSmallRest.GGTwF4RankInput) (hT : TableBExcSmallRest.GGTitsThreeRankInput)
    (h : GGStdSubPreInputOn GGTableBOtherRestNoSmall) :
    GGStdSubPreInputOn GGTableBOtherRest4NoF4 :=
  ((ggStdSubPreInputOn_smallRest h3 hF hT).or h).mono fun p lab _ _ hl => by
    by_cases hS : TableBExcSmallRest.GGTableBExcSmallRestLabel p lab
    exacts [Or.inl hS, Or.inr ⟨hl, hS⟩]

end RoundFour

end CFSG.StandardType
