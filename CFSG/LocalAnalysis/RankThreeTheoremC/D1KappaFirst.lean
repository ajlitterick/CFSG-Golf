module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KExtremal
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaTop
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineShared
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.AGLEmbeddingD2
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]


theorem normalizer_le_of_isAGLQ_of_escape {p : ℕ} {P : Sylow p G} {M H R U : Subgroup G}
    (he : D1Escape p P M H R) (hU : IsAGLQ p M U) : Subgroup.normalizer (U : Set G) ≤ M := by
  obtain ⟨K, R', hx⟩ := he.exists_extremal
  exact normalizer_le_of_isAGLQ hx hU


end CFSG.LocalAnalysis.RankThreeTheoremC
