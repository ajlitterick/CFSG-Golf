module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)

section Transport


end Transport


theorem dualRoot_rootR_rootS_root1221_root1242 :
    ReeTag.F4.dualRoot rootR = rootS ∧ ReeTag.F4.dualRoot rootS = rootR ∧
      ReeTag.F4.dualRoot root1221 = root1242 ∧ ReeTag.F4.dualRoot root1242 = root1221 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

section Roots


end Roots


section Pairs


end Pairs

section Weyl


end Weyl

section Phi


end Phi


end CFSG.SeitzReduction.F4Pilot
