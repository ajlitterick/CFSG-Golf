module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111E16

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81ElevenTwelveOne (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    3 ∈ rankThreeSigmaA G → AGL81CfgData 3 P M H Q K → IsAltTwoP 3 K →
    ¬ HasPrimeConstraint (G := H) 3 →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∃ I₀ ∈ cZero (H ⊓ L), CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre 3 H K) →
    Open.pRank 3 H ≤ 2


end CFSG.LocalAnalysis.RankThreeTheoremC
