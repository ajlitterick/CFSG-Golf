module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySix
public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupRankTwoCharSubgroupOf
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Generic

variable {X : Type} [Group X] [Finite X]


theorem center_eq_bot_of_isLinThreeFour {K : Type} [Group K] (h : IsLinThreeFour K) :
    Subgroup.center K = ⊥ := by
  have := isSimpleGroup_of_isLinThreeFour' h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hb | ht
  · exact hb
  · exfalso
    let : CommGroup K := { ‹Group K› with
      mul_comm := fun a b => (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top a) b).symm }
    have hp := IsSimpleGroup.prime_card (α := K)
    rw [card_of_isLinThreeFour h] at hp
    exact absurd hp (by norm_num)


end Generic

section Image


end Image

section Main

open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2


end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
