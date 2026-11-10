module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataScalarPairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CatalogueBDerivedNormalSection

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem matrixDerivedPairs_eq_sectionDerived (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q = derivedNormalSubgroup (matrixIsometryPairs Q) := by
  rw [matrixDerivedPairs_eq_commutator, derivedNormalSubgroup_eq]


theorem matrixProjectiveConjugationHom_derived (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) =
      MulAut.conj (matrixProjectiveProjection Q A) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q (matrixDerivedInclusion Q A)
    (matrixProjectiveProjection Q B) = _
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem matrixProjective_inner_le_image (Q : QuadraticForm K (Fin d → K)) :
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ matrixProjectiveImage Q := by
  rintro alpha ⟨x, rfl⟩
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  exact ⟨matrixDerivedInclusion Q A, matrixProjectiveConjugationHom_derived Q A⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
