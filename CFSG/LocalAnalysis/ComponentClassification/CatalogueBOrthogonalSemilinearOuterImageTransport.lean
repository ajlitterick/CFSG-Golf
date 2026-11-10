module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImageBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixInnerQuotientAction (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q →* MatrixImageInnerQuotient Q :=
  (matrixImageInnerProjection Q).comp (matrixProjectiveConjugationHom Q).rangeRestrict


theorem matrixInnerQuotientAction_surjective (Q : QuadraticForm K (Fin d → K)) :
    Function.Surjective (matrixInnerQuotientAction Q) :=
  (QuotientGroup.mk'_surjective (matrixImageInner Q)).comp
    (MonoidHom.rangeRestrict_surjective (matrixProjectiveConjugationHom Q))


end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage
