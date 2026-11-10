module

import CFSG.RankThree.LocalRank.InvariantPrimeComplementOdd
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type*} [Group G] [Finite G]


omit [Finite G] in
theorem le_normalizer_map_subtype {H : Subgroup G} (K : Subgroup H) [K.Normal] :
    H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := K) H.subtype
  rwa [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h


end CFSG.RankThree.PartTwo.Sec6
