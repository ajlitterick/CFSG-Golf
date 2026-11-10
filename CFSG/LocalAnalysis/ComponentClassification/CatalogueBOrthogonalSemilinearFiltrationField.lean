module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem fieldProjection_range_cyclic [Finite K]
    (Q : QuadraticForm K (Fin d → K)) : IsCyclic (fieldProjection Q).range := by
  let : IsCyclic (K ≃+* K) := CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  infer_instance

@[expose] def fieldQuotientEquivRange (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q ⧸ linearSimilarityPairs Q ≃* (fieldProjection Q).range :=
  QuotientGroup.quotientKerEquivRange (fieldProjection Q)


theorem fieldQuotient_cyclic [Finite K] (Q : QuadraticForm K (Fin d → K)) :
    IsCyclic (similarityPairs Q ⧸ linearSimilarityPairs Q) := by
  let : IsCyclic (fieldProjection Q).range := fieldProjection_range_cyclic Q
  exact (fieldQuotientEquivRange Q).isCyclic.mpr inferInstance

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
