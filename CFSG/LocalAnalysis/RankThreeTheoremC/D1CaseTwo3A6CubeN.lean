module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexOrbit
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Bound
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def CenterCentralizesBlockV {G : Type} [Group G] (X S L : Subgroup G)
    (hLX : L ≤ X) : Prop :=
  ∀ c (hc : c ∈ L), QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨c, hLX hc⟩ ∈
      Subgroup.centralizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) →
    ∀ v ∈ blockV S L, c * v = v * c


end CFSG.LocalAnalysis.RankThreeTheoremC
