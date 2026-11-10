module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {r f : ℕ} {K : Type*} [Field K] (h : UnitaryFieldData r f K)

section ConjTranspose

variable {ι : Type*}


theorem conjT_one [DecidableEq ι] : ((1 : Matrix ι ι K).map h.bar)ᵀ = 1 := by
  rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]


end ConjTranspose


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
