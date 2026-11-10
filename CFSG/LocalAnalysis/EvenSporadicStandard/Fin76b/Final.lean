
module


public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65Facts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem fin76bLemma65b_of_residuals
    (h1 : Fin76bNoOrderEight) (h2 : Fin76bNoKleinFour) : Fin76bLemma65b :=
  fin76bLemma65b_of_bound fin76bWFacts (fin76bBound_of_residuals h1 h2)


end CFSG.EvenSporadicStandard.Fin76b
