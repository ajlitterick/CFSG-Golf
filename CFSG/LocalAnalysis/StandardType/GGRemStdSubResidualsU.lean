module

public import CFSG.Yardstones.M3f9567aba59d.StdSubTableB
public import CFSG.LocalAnalysis.StandardType.GGYardstoneHeaderImports
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesJ1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesZ7

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderStdSubTableB_of_residualsU
    (hTE6 : GGTableBTwE6Round12Lang)
    (hPR : GGStdSubIOneProperInputOn GGIOneProperRestNarrowLabel)
    (hsR : GGStdSubSmallInputOn GGStdSubSmallRest5Label)
    (hLC : GGLayerCenterCyclicModelRestTwo) :
    GGRemainderStdSubTableB :=
  ⟨hTE6, hPR, ggStdSubSmallInputOn_rest4_of_not_unitDvd hsR, hLC⟩

end CFSG.Yardstones.M3f9567aba59d
