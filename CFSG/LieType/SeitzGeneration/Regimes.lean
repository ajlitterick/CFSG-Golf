module

public import CFSG.LieType.SeitzGeneration.Dispatch

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def IsDFourIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .D 4 q

@[expose] def SeitzInnerThreeClassical : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsClassicalIndex d.1

@[expose] def SeitzInnerThreeExceptional : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ ¬ IsClassicalIndex d.1

theorem seitzInnerThree_of_regimes (hc : SeitzInnerThreeClassical)
    (hx : SeitzInnerThreeExceptional) : SeitzInnerThree :=
  SeitzPlanes.of_cover (fun d _ _ _ E hE => by
    by_cases h : IsClassicalIndex d.1
    exacts [Or.inl ⟨hE.1, hE.2, h⟩, Or.inr ⟨hE.1, hE.2, h⟩]) hc hx

@[expose] def SeitzOuterClassical : Prop :=
  SeitzPlanes fun d p E =>
    ¬ InnerPlane d p E ∧ IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)

@[expose] def SeitzOuterExceptional : Prop :=
  SeitzPlanes fun d p E =>
    ¬ InnerPlane d p E ∧ (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1))

theorem kFactSeitzRankTwoOuter_of_regimes (hc : SeitzOuterClassical)
    (hx : SeitzOuterExceptional) : KFactSeitzRankTwoOuter :=
  SeitzPlanes.of_cover (fun d p _ _ E hE => by
    by_cases h : IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)
    · exact Or.inl ⟨hE, h.1, h.2⟩
    · refine Or.inr ⟨hE, ?_⟩
      by_cases h1 : IsClassicalIndex d.1
      · exact Or.inr (by by_contra h2; exact h ⟨h1, h2⟩)
      · exact Or.inl h1) hc hx

@[expose] def SeitzInnerLow : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d)

@[expose] def SeitzOuterLow : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE2 p (Cat d)


theorem KFactSeitzRankTwoLow.inner (h : KFactSeitzRankTwoLow) : SeitzInnerLow :=
  SeitzPlanes.mono (fun _ _ _ hE => hE.2) h

theorem KFactSeitzRankTwoLow.outer (h : KFactSeitzRankTwoLow) : SeitzOuterLow :=
  SeitzPlanes.mono (fun _ _ _ hE => hE.2) h

theorem KFactSeitzRankTwoInner.low (h : KFactSeitzRankTwoInner) : SeitzInnerLow :=
  SeitzPlanes.mono (fun _ _ _ hE => hE.1) h

theorem KFactSeitzRankTwoOuter.low (h : KFactSeitzRankTwoOuter) : SeitzOuterLow :=
  SeitzPlanes.mono (fun _ _ _ hE => hE.1) h

@[expose] def KFactSeitzRankTwoInnerEx : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 →
    (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E


end CFSG.LieType.SeitzGeneration
