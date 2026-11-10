module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassesC3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Roots


theorem C3Set_eq_c3LeviRoots : C3Set = c3LeviRoots :=
  Set.ext fun _ => mem_C3Set_iff

theorem C3Set_eq_c3PerpRoots : C3Set = c3PerpRoots :=
  Set.ext fun _ => mem_C3Set_iff.trans mem_c3PerpRoots_iff.symm

end Roots

variable {K : Type} [Field K]

section Levi


theorem C3Levi_eq_subgroupOf_rootSpan_C3Set :
    C3Levi K = (rootSpan .F4 K C3Set).subgroupOf (adjointGroup .F4 K) := by
  rw [C3Set_eq_c3LeviRoots]
  rfl


end Levi


end CFSG.SeitzReduction.F4Pilot
