module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1ConstrainedCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → HasPrimeConstraint (G := H) p → False


end CFSG.AGLEmbedding
