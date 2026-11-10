module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointKernelProjective
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNormalizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear
open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Classical

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem projectivePointStabilizer_eq_actionStabilizer
    (Q : QuadraticForm K (Fin d → K)) (L : CatalogueBOrthogonalPointAction.Points Q) :
    projectivePointStabilizer Q L =
      CatalogueBOrthogonalPointAction.actionStabilizer Q (projectivePointAction Q) L := by
  ext g
  rfl

theorem projective_point_action_properties (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) :
    CatalogueBOrthogonalPointAction.ActionProperties Q (projectivePointAction Q) :=
  CatalogueBOrthogonalPointAction.actionProperties_equiv Q _ _
    (matrixNativeProjectiveEquiv Q hE) (projectivePointAction_native Q hE)
    (CatalogueBOrthogonalPointAction.projective_action_properties Q hQ hT)

theorem projectivePointStabilizer_injective_native (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) :
    Function.Injective (projectivePointStabilizer Q) := by
  have h := (projective_point_action_properties Q hE hQ hT).2.2.2.2.2.1
  intro L M hLM
  apply h
  simpa only [← projectivePointStabilizer_eq_actionStabilizer] using hLM


end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
