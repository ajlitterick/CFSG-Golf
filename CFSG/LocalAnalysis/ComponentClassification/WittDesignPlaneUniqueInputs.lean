module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneFrame
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
public import CFSG.Monster.B.Classical.PlaneIncidence
public meta import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
public meta import Mathlib

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open Equiv CFSG.Monster.B.Classical.Plane

@[expose] def enc (j : Fin 5) (x : Fin 4) : Fin 21 := ⟨1 + 4 * j + x, by omega⟩


section Squares


end Squares

end CFSG.ComponentClassification.WittDesign
