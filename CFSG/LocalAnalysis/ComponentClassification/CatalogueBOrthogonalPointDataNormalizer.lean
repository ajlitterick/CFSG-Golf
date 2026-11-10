module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction
open CatalogueBStabilizerFamily

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def projectivePointNormalizer (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (Equiv.Perm (Points Q)) := imageNormalizer (projectivePointAction Q)

@[expose] def pointFamilyNormalizerEquiv (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    projectivePointFamilyAut Q ≃* projectivePointNormalizer Q :=
  normalizerEquiv (projectivePointAction Q) hrho hs


theorem pointFamilyNormalizerEquiv_similarity (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) (g : similarityPairs Q) :
    (pointFamilyNormalizerEquiv Q hrho hs
      ⟨matrixProjectiveConjugationHom Q g,
        projective_image_le_pointFamilyAut Q ⟨g, rfl⟩⟩).val =
      similarityPointAction Q g :=
  pointPerm_of_covariance (projectivePointAction Q) hs (matrixProjectiveConjugationHom Q g)
    (similarityPointAction Q g) (similarity_projective_covariance Q g)


theorem pointFamilyNormalizerEquiv_similarity_image (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    ((matrixProjectiveImage Q).subgroupOf (projectivePointFamilyAut Q)).map
        (pointFamilyNormalizerEquiv Q hrho hs).toMonoidHom =
      (similarityPointImage Q).subgroupOf (projectivePointNormalizer Q) :=
  compatible_image (projectivePointAction Q) hrho hs (matrixProjectiveConjugationHom Q)
    (similarityPointAction Q) (similarity_projective_covariance Q)


end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
