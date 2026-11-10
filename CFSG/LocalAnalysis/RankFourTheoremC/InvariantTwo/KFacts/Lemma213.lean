module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213CaseB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Signalizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms Subgroup

namespace Red

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem outer_solvable (R : Red n p K P z D) (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections K) (C : ComponentIndex K) :
    Group.IsSolvable (Outer C.1) := by
  obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C
  exact hS C.1 hsimple hnonab (hcat.simple_subgroup C.1 hsimple hnonab)

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG CFSG.LocalCores CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 Subgroup


end CFSG.LocalAnalysis.RankFourTheoremC
