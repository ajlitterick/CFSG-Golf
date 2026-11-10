module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}


@[expose] def matrixImageInner (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (matrixProjectiveImage Q) :=
  (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf (matrixProjectiveImage Q)


instance matrixImageInner_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixImageInner Q).Normal := by
  unfold matrixImageInner
  infer_instance


abbrev MatrixImageInnerQuotient (Q : QuadraticForm K (Fin d → K)) :=
  matrixProjectiveImage Q ⧸ matrixImageInner Q

@[expose] def matrixImageInnerProjection (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveImage Q →* MatrixImageInnerQuotient Q := QuotientGroup.mk' _


end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage
