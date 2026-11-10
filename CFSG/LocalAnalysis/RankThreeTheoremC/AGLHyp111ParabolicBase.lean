module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111FactorAtBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_of_le_normalizer {N K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (K ⊔ N) = N.relIndex K := by
  set A := K ⊔ N
  have hNA : N ≤ A := le_sup_right
  have hKA : K ≤ A := le_sup_left
  set N' := N.subgroupOf A
  set K' := K.subgroupOf A
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr
    (sup_le hK Subgroup.le_normalizer)
  have htop : K' ⊔ N' = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKA,
      Subgroup.map_subgroupOf_eq_of_le hNA, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show N'.index = _
  rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right,
    Subgroup.relIndex_subgroupOf hKA]


end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
