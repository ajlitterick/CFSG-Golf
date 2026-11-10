module

public import CFSG.LieType.SeitzGeneration.Regimes

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def NormalizesRSubgroup (d : TauCeti.ValidLieTypeIndex)
    (E : Subgroup (MulAut (Cat d))) : Prop :=
  ∃ R : Subgroup (Cat d), R ≠ ⊥ ∧ IsPGroup d.1.characteristic R ∧
    ∀ ε ∈ E, R.map ε.toMonoidHom = R

@[expose] def SeitzExcParabolic : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ ¬ IsClassicalIndex d.1 ∧ NormalizesRSubgroup d E

@[expose] def ExcParabolicPlane : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 → ¬ IsClassicalIndex d.1 → ¬ RankLE2 p (Cat d) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ NormalizesRSubgroup d E

@[expose] def SeitzExcAnisotropic : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ ¬ IsClassicalIndex d.1 ∧ RankLE2 p (Cat d) ∧ ¬ NormalizesRSubgroup d E


@[expose] def SeitzInnerLowClassical : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsClassicalIndex d.1


@[expose] def InnerExFor (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), P d → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    p ≠ d.1.characteristic → ¬ IsD2SeitzException p d.1 →
    (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E

theorem kFactSeitzRankTwoInnerEx_of_for (hc : InnerExFor fun d => IsClassicalIndex d.1)
    (hx : InnerExFor fun d => ¬ IsClassicalIndex d.1) : KFactSeitzRankTwoInnerEx := by
  intro d p hp hp2 hpd hex hE
  by_cases h : IsClassicalIndex d.1
  · exact hc d h p hp hp2 hpd hex hE
  · exact hx d h p hp hp2 hpd hex hE

theorem seitzExcLow_of (hPar : SeitzExcParabolic) (hAni : SeitzExcAnisotropic) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ ¬ IsClassicalIndex d.1 :=
  fun d p hp hp2 hpd hex E hE hc ⟨hi, hr, hx⟩ => by
    by_cases hN : NormalizesRSubgroup d E
    · exact hPar d p hp hp2 hpd hex E hE hc ⟨hi, hx, hN⟩
    · exact hAni d p hp hp2 hpd hex E hE hc ⟨hi, hx, hr, hN⟩


end CFSG.LieType.SeitzGeneration
