module

public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem isQuasisimple_of_mem_thetaComponents_of_le_center {H : Type*} [Group H] {p : ℕ}
    {L : Subgroup H} (hL : L ∈ thetaComponents p H)
    (hZ : aschbacherSolvableCore p L ≤ Subgroup.center L) : IsQuasisimple L := by
  have hq := LocalCores.quasisimple_central_extension_derived (aschbacherSolvableCore p L) hZ
    hL.2.2
  have htop : commutator L = ⊤ := Group.isPerfect_def.mp hL.1
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hq


end CFSG.RankThree.GroupTheory
