module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNormalizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

open CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction CatalogueBStabilizerFamily

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}


@[expose] def statedPointStabilizer {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) (L : Points Q) : Subgroup (StatedProj (StatedOmega Q0)) :=
  pointStabilizer (statedPointAction hQ) L

theorem mem_statedPointStabilizer_iff {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) (L : Points Q) (g : StatedProj (StatedOmega Q0)) :
    g ∈ statedPointStabilizer hQ L ↔ statedPointAction hQ g L = L := Iff.rfl

theorem statedPointStabilizer_reindex_comap (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) (L : Points Q) :
    (CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) (reindexPointEquiv eI Q L)).comap
        (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom = statedPointStabilizer hQ L := by
  ext g
  change CatalogueBOrthogonalPointData.projectivePointAction _
    (statedProjectiveReindexEquiv eI Q hQ g) (reindexPointEquiv eI Q L) =
    reindexPointEquiv eI Q L ↔ statedPointAction hQ g L = L
  rw [← statedPointAction_reindex eI Q hQ g L]
  exact (reindexPointEquiv eI Q).injective.eq_iff

theorem statedPointStabilizer_reindex_map (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) (L : Points Q) :
    (statedPointStabilizer hQ L).map (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom =
      CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) (reindexPointEquiv eI Q L) := by
  rw [← statedPointStabilizer_reindex_comap eI Q hQ L]
  exact Subgroup.map_comap_eq_self_of_surjective (statedProjectiveReindexEquiv eI Q hQ).surjective _


@[expose] def statedPointFamily {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) : Set (Subgroup (StatedProj (StatedOmega Q0))) :=
  family (statedPointAction hQ)

theorem statedPointFamily_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (fun U => U.map (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom) '' statedPointFamily hQ =
      CatalogueBOrthogonalPointData.projectivePointFamily
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) := by
  ext U
  constructor
  · rintro ⟨T, ⟨L, rfl⟩, rfl⟩
    exact ⟨reindexPointEquiv eI Q L, (statedPointStabilizer_reindex_map eI Q hQ L).symm⟩
  · rintro ⟨L, rfl⟩
    refine ⟨statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L),
      ⟨(reindexPointEquiv eI Q).symm L, rfl⟩, ?_⟩
    change (statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L)).map
      (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom =
      CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) L
    rw [statedPointStabilizer_reindex_map eI Q hQ, Equiv.apply_symm_apply]


end CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
