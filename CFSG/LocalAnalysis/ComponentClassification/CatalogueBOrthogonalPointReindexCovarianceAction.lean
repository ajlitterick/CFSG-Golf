module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionStated
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem statedDerivedPointAction_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) (L : Points Q) :
    reindexPointEquiv eI Q (statedDerivedPointAction hQ A L) =
      CatalogueBOrthogonalPointData.derivedPointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedDerivedReindexEquiv eI Q hQ A) (reindexPointEquiv eI Q L) := by
  apply Subtype.ext
  rw [reindexPointEquiv_submodule]
  change (orthogonalPointAction Q (statedOrthogonalHom hQ A) L).val.map _ = _
  rw [orthogonalPointAction_submodule,
    CatalogueBOrthogonalPointData.derivedPointAction_submodule,
    reindexPointEquiv_submodule]
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨CatalogueBOrthogonalPointData.reindexVectorEquiv eI x, ⟨x, hx, rfl⟩, ?_⟩
    exact statedDerivedReindexEquiv_vector eI Q hQ A x
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨toLinEquiv ι K A.val x, ⟨x, hx, rfl⟩, ?_⟩
    exact (statedDerivedReindexEquiv_vector eI Q hQ A x).symm


theorem statedPointAction_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : StatedProj (StatedOmega Q0)) (L : Points Q) :
    reindexPointEquiv eI Q (statedPointAction hQ g L) =
      CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedProjectiveReindexEquiv eI Q hQ g) (reindexPointEquiv eI Q L) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [statedProjectiveReindexEquiv_mk, CatalogueBOrthogonalPointData.projectivePointAction_mk]
  change reindexPointEquiv eI Q (statedDerivedPointAction hQ A L) = _
  exact statedDerivedPointAction_reindex eI Q hQ A L


end CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
