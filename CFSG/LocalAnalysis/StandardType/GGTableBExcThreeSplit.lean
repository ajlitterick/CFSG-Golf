module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRest

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggBstarInputOn_E7E8_split_holds : GGBstarInputOn GGTableBE7E8Label :=
  ggBstarInputOn_E7E8_split ggE7ThreeToralRankInput_holds ggE8ThreeToralRankInput_holds

theorem ggStdSubPreInputOn_E7E8_split_holds : GGStdSubPreInputOn GGTableBE7E8Label :=
  ggStdSubPreInputOn_E7E8_split ggE7ThreeToralRankInput_holds ggE8ThreeToralRankInput_holds


end CFSG.StandardType
