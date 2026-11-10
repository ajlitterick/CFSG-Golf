
module


public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransferJ

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem fin76bLemma65b_of_noKleinFour
    (h2 : Fin76bNoKleinFour) : Fin76bLemma65b :=
  fin76bLemma65b_of_residuals fin76bNoOrderEight h2


end CFSG.EvenSporadicStandard.Fin76b
