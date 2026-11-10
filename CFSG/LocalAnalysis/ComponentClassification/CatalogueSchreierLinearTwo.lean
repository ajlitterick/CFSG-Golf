module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter OuterAutomorphisms

universe u v

@[expose] def coordinateOuterEquivPSL (K : Type u) [Field K] :
    Outer (coordinateG K) ≃* Outer (PSL2 K) :=
  equivalence (pslEquivCoordinateG K).symm


@[expose] def projectiveOuterEquivCoordinate (K : Type u) [Field K] :
    Outer (ProjectiveQuotient K) ≃* Outer (coordinateG K) :=
  equivalence (projectiveQuotientEquivCoordinateG K)


@[expose] def coordinateOuterQuotientEquiv (K : Type u) [Field K] [Finite K] :
    CoordinateQuotientEG K ≃* Outer (coordinateG K) :=
  QuotientGroup.congr ((coordinateG K).subgroupOf (coordinateE K))
    (inner (coordinateG K)) (coordinateConjugationEquiv K)
    (coordinateConjugation_G_image K)


theorem coordinateOuter_secondDerived_eq_bot (K : Type u) [Field K] [Finite K] :
    derivedSeries (Outer (coordinateG K)) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (coordinateOuterQuotientEquiv K).toMonoidHom
    (coordinateOuterQuotientEquiv K).surjective (coordinateEG_secondDerived_eq_bot K)


theorem projectiveOuter_secondDerived_eq_bot (K : Type u) [Field K] [Finite K] :
    derivedSeries (Outer (ProjectiveQuotient K)) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (projectiveOuterEquivCoordinate K).symm.toMonoidHom
    (projectiveOuterEquivCoordinate K).symm.surjective
    (coordinateOuter_secondDerived_eq_bot K)


end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
