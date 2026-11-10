module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImageTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage

open CatalogueBOrthogonalSemilinear CatalogueBDerivedNormalSection

universe u

variable {K : Type u} [Field K] {d : ℕ}


theorem matrixDerivedPairs_le_innerQuotientKernel (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q ≤ (matrixInnerQuotientAction Q).ker := by
  rintro g ⟨A, rfl⟩
  change matrixImageInnerProjection Q ((matrixProjectiveConjugationHom Q).rangeRestrict
    (matrixDerivedInclusion Q A)) = 1
  apply (QuotientGroup.eq_one_iff (N := matrixImageInner Q) _).mpr
  change matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) ∈
    OuterAutomorphisms.inner (matrixProjectiveDerived Q)
  exact ⟨matrixProjectiveProjection Q A, (matrixProjectiveConjugationHom_derived Q A).symm⟩

theorem matrixInnerQuotientAction_derivedSeries_bot_of_quotient
    (Q : QuadraticForm K (Fin d → K)) (r : ℕ)
    (hquotient : derivedSeries (similarityPairs Q ⧸ matrixIsometryPairs Q) r = ⊥) :
    derivedSeries (MatrixImageInnerQuotient Q) (r + 1) = ⊥ := by
  have hderived : derivedSeries (similarityPairs Q) (r + 1) ≤ matrixDerivedPairs Q := by
    rw [matrixDerivedPairs_eq_sectionDerived]
    exact derivedSeries_succ_le_derivedNormalSubgroup (matrixIsometryPairs Q) r hquotient
  rw [← map_derivedSeries_eq (matrixInnerQuotientAction_surjective Q)]
  exact (Subgroup.map_eq_bot_iff _).mpr
    (hderived.trans (matrixDerivedPairs_le_innerQuotientKernel Q))


theorem matrixImageInnerQuotient_thirdDerived [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    derivedSeries (MatrixImageInnerQuotient Q) 3 = ⊥ :=
  matrixInnerQuotientAction_derivedSeries_bot_of_quotient Q 2
    (CatalogueBOrthogonalSemilinearFiltration.similarityIsometryQuotient_secondDerived Q
      (CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value Q hQ))


end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage
