module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag

variable {r f : ℕ} {K : Type} [Field K]

theorem finite_mulAut_hypPSU (h : UnitaryFieldData r f K) (a ε : ℕ) :
    Finite (MulAut (hypPSU h a ε)) := by
  have := h.finite
  exact Finite.of_injective (fun α : MulAut (hypPSU h a ε) => (α : hypPSU h a ε → hypPSU h a ε))
    fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)


end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
