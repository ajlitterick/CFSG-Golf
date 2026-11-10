module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem largeEvenRawDatum_or {lab : LargeEvenLabel} {Q₁ Q₂ : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab fun R _ I F => Q₁ R I F ∨ Q₂ R I F) :
    LargeEvenRawDatum lab Q₁ ∨ LargeEvenRawDatum lab Q₂ := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       rcases hq with hq | hq
       exacts [Or.inl ⟨K, i1, i2, hK, b, c, hbc, hq⟩, Or.inr ⟨K, i1, i2, hK, b, c, hbc, hq⟩])
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       rcases hq with hq | hq
       exacts [Or.inl ⟨K, i1, i2, hK, hq⟩, Or.inr ⟨K, i1, i2, hK, hq⟩])

theorem largeEvenMarking_or {X : Type*} [Group X] {P Q : LargeEvenMarkProp X}
    (h : LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∨ Q lab R I F θ) :
    LargeEvenMarking X P ∨ LargeEvenMarking X Q := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' : LargeEvenRawDatum lab fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P lab R I F θ) ∨
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, Q lab R I F θ) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ | hθ⟩
    exacts [Or.inl ⟨hs, hna, θ, hθ⟩, Or.inr ⟨hs, hna, θ, hθ⟩]
  rcases largeEvenRawDatum_or hraw' with h' | h'
  exacts [Or.inl ⟨hX, lab, hlab, h'⟩, Or.inr ⟨hX, lab, hlab, h'⟩]

section Inputs


end Inputs

end CFSG.StandardType
