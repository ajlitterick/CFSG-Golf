module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley

theorem a5LeviRoots_eq_perpRoots : a5LeviRoots = EPilot.perpRoots .E6 :=
  rfl


theorem a5Levi_eq_subgroupOf_perpRoots (K : Type) [Field K] :
    a5Levi K = (rootSpan .E6 K (EPilot.perpRoots .E6)).subgroupOf (adjointGroup .E6 K) :=
  rfl


end CFSG.SeitzReduction.E6Pilot
