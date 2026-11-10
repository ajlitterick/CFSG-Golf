module

public import CFSG.ClassicalInvolution.SmallCases.Partition
import CFSG.ClassicalInvolution.RankTwo

public section

namespace CFSG.ClassicalInvolution

theorem citRankTwo : CITRankTwo := fun F _ _ _ hnab z hz K hzK hK hw hns h2 =>
  oddLieType_or_m11_of_twoRank_le_two F hnab h2 z hz K hzK hK hw hns


end CFSG.ClassicalInvolution
