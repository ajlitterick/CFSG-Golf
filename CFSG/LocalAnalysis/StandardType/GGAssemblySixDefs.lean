module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusion
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGLayerPDivRound6 : Prop :=
  GGLayerPDivTag .F4 ∧ GGLayerPDivTag .E6 ∧ GGLayerPDivTag .E7 ∧ GGLayerPDivTag .E8 ∧
    GGLayerPDivTag .twistedE6

theorem ggLayerPDivInput_of_round6 (h : GGLayerPDivRound6) : GGLayerPDivInput :=
  ggLayerPDivInput_of_remaining_five h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2


end Lie

section HypSix


end HypSix


@[expose] def GGTableBOtherRound6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRound5 p lab ∧ ¬ (lab.tag = .E6 ∧ p = 3)

theorem ggTableBOtherRound6_twE6 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRound6 p lab) (hs : LargeEvenSplit p lab) :
    lab.tag = .twE6 := by
  obtain ⟨⟨h4, hF4, hE6, hE78, hS⟩, hE3⟩ := h
  rcases ggTableBOtherRest4_cases hp hlab h4 hs with ht | ht | ht | ht | ht | ht |
    ⟨ht | ht | ht, -⟩
  · refine absurd ⟨ht, ?_⟩ hE3
    rcases (largeEvenSplit_E_iff (Or.inl ht)).mp hs with hd | hd
    · by_contra hp3
      exact hE6 ⟨ht, hd, hp3⟩
    · exact hd.2
  · exact ht
  · exact absurd (Or.inl ht) hS
  · exact absurd (Or.inr (Or.inl ht)) hS
  · exact absurd (Or.inr (Or.inr (Or.inl ht))) hS
  · exact absurd (Or.inr (Or.inr (Or.inr ht))) hS
  · exact absurd ⟨ht, hs⟩ hF4
  · exact absurd ⟨Or.inl ht, hs⟩ hE78
  · exact absurd ⟨Or.inr ht, hs⟩ hE78

section TableBE6

theorem ggBstarInputOn_round5_of_round6 (h : GGBstarInputOn GGTableBOtherRound6) :
    GGBstarInputOn GGTableBOtherRound5 :=
  (ggBstarInputOn_E6_three.or h).mono_split fun p lab hR hs => by
    by_cases hE : lab.tag = .E6 ∧ p = 3
    · exact Or.inl (ggTableBE6LabelThree_of_split hE.1 hE.2 hs)
    · exact Or.inr ⟨hR, hE⟩


theorem ggTableBSmallRankRound5_of_round6
    (h : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGTableBSmallRankRound5 :=
  ⟨TableBExcSmallRanks.ggTriD4ThreeRankInput_holds, TableBExcSmallRanks.ggTwF4RankInput_of_three h,
    TableBExcSmallRest.ggTitsThreeRankInput_holds⟩

end TableBE6

section TableB

theorem ggBstarInputOn_rest4_of_round6 (hS : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGBstarInputOn GGTableBOtherRound6) : GGBstarInputOn GGTableBOtherRest4 :=
  ggBstarInputOn_rest4_of_round5 (ggTableBSmallRankRound5_of_round6 hS)
    (ggBstarInputOn_round5_of_round6 h)


end TableB

@[expose] def GGTableBNbrInnerRound6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoRestLabel p lab ∧ ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ GGTableBF4Label p lab

section NbrInner

theorem ggTableBNbrInnerInput_of_round6
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_rest_F4 h

end NbrInner

end CFSG.StandardType
