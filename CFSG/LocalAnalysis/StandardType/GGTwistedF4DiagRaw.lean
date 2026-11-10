module

public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGRawAutRest

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggRawInnFieldOn_rest5 :
    GGRawInnFieldOn fun lab => ¬ GGRawInnFieldDoneLabel lab ∧ ¬ GGOmegaLabel lab :=
  ggRawInnFieldOn_rest5_of_diag ggTwistedF4DiagInput_holds

theorem ggRawInnFieldInput_holds : GGRawInnFieldInput :=
  ggRawInnFieldInput_of_twF4Diag ggTwistedF4DiagInput_holds

end CFSG.StandardType
