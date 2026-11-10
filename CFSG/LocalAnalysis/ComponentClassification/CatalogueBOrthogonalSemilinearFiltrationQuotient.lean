module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationField

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}


theorem linear_commutator_le_isometry (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) :
    ⁅linearSimilarityPairs Q, linearSimilarityPairs Q⁆ ≤ matrixIsometryPairs Q := by
  have h : commutator (linearSimilarityPairs Q) ≤
      (matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q) := by
    rw [← multiplierHom_kernel Q hQ]
    exact Abelianization.commutator_subset_ker (multiplierHom Q hQ)
  have hm := Subgroup.map_mono (f := (linearSimilarityPairs Q).subtype) h
  simpa only [commutator, Subgroup.map_commutator, Subgroup.map_top,
    Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le (matrixIsometryPairs_le_linearPairs Q)] using hm

theorem similarity_commutator_le_linear [Finite K] (Q : QuadraticForm K (Fin d → K)) :
    commutator (similarityPairs Q) ≤ linearSimilarityPairs Q := by
  let : IsCyclic (fieldProjection Q).range := fieldProjection_range_cyclic Q
  have h := Abelianization.commutator_subset_ker (fieldProjection Q).rangeRestrict
  rwa [MonoidHom.ker_rangeRestrict] at h

abbrev SimilarityIsometryQuotient (Q : QuadraticForm K (Fin d → K)) :=
  similarityPairs Q ⧸ matrixIsometryPairs Q

theorem similarity_secondDerived_le_isometry [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    derivedSeries (similarityPairs Q) 2 ≤ matrixIsometryPairs Q := by
  change ⁅commutator (similarityPairs Q), commutator (similarityPairs Q)⁆ ≤ _
  exact (Subgroup.commutator_mono (similarity_commutator_le_linear Q)
    (similarity_commutator_le_linear Q)).trans (linear_commutator_le_isometry Q hQ)

theorem similarityIsometryQuotient_secondDerived [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    derivedSeries (SimilarityIsometryQuotient Q) 2 = ⊥ := by
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (matrixIsometryPairs Q))]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  exact similarity_secondDerived_le_isometry Q hQ


end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
