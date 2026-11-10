module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] {n : ℕ}

noncomputable abbrev minusRadical (hn : 1 ≤ n) (b c : K) (i j : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  rootRadicalBar (coordinateQuadMinus n K hn b c) (isHypCoord_coordinateQuadMinus hn b c i).hypPair
    (isHypCoord_coordinateQuadMinus hn b c j).hypPair

noncomputable abbrev minusLevi (hn : 1 ≤ n) (b c : K) (i j : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  rootLeviBar (coordinateQuadMinus n K hn b c) (isHypCoord_coordinateQuadMinus hn b c i).hypPair
    (isHypCoord_coordinateQuadMinus hn b c j).hypPair


end CFSG.SeitzReduction.OmegaPilot
