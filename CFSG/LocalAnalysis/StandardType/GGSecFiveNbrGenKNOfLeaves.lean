module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrGuardOfEnnola

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Leaves

theorem s2jn_ggSecFiveNbrGenKNInput'_of_leaves
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hKn : GGTCJEnnolaKnown) (hP : GGStdSubPrimeInput) (hcore : GGJRootCoreInput) :
    GGSecFiveNbrGenKNInput' :=
  s2jn_ggSecFiveNbrGenKNInput' s2jn_ggSecFiveKGPosNbrInput'_holds
    (s2jn_ggSecFiveSplitNbrGuardInput' hKn (ggLBalanceInput_of_catalogueSchreier hSch) hP)
    (ggNbrSubcomponentInput_of_catalogueSchreier hSch hP)
    (s2jn_ggSecFiveJReflInput'_of_core hcore) s2jn_ggSecFiveJNormDInput'_holds

end Leaves

end CFSG.StandardType

end
