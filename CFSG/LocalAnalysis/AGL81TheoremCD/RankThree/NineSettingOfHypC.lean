module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.TheoremCThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {G : Type} [Group G] [Finite G]

namespace RankThree


end RankThree

namespace Section14.HypCGen

variable {M : Subgroup G} {q : ℕ} {E H : Subgroup G}


theorem not_mem_sigmaM (h : HypCGen G M q E H) :
    q ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
  simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
    CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet


end Section14.HypCGen

namespace RankThree


end RankThree

end CFSG.LocalAnalysis.AGL81TheoremCD
