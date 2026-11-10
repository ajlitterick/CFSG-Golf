module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}


theorem hypSU_le_hypUnitary : hypSU h r ε ≤ hypUnitary h r ε :=
  fun _ hg => hg.1


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
