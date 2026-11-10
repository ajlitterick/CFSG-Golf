module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixScalarPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (similarityPairs Q) :=
  (matrixDerivedScalars Q).map (matrixDerivedInclusion Q)


instance matrixScalarPairs_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixScalarPairs Q).Normal where
  conj_mem n hn g := by
    obtain ⟨A, hA, rfl⟩ := hn
    refine ⟨matrixDerivedConjugation Q g A, ?_, matrixDerivedInclusion_conjugation Q g A⟩
    rw [← matrixDerivedScalars_invariant Q g]
    exact Subgroup.mem_map_of_mem (matrixDerivedConjugation Q g).toMonoidHom hA


@[expose] def matrixPairScalars (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (matrixDerivedPairs Q) :=
  (matrixScalarPairs Q).subgroupOf (matrixDerivedPairs Q)

instance matrixPairScalars_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixPairScalars Q).Normal := by
  unfold matrixPairScalars
  infer_instance


end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
