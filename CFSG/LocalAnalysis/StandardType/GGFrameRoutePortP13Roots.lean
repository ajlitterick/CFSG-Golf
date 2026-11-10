module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRoots
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRootsAux

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.OddStandard.SmallF3.Omega.E7RootSet


theorem p13a2_E7_redV_ne_zero (α : Fin Tag.E7.rank → ℤ) (hα : IsRoot Tag.E7 α) :
    redV α ≠ 0 := by
  have key : ∀ v ∈ e7RootsP1_certVecs, redV v ≠ 0 := by decide +kernel
  exact key α ((e7RootsP1_isRoot_iff α).mp hα)

end CFSG.StandardType.FrameRoute
