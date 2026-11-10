module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfP45
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.ComponentClassification.GSThmB

theorem cfQ3Conf : CFQ3Conf := by
  intro K₀ _ _ hK c
  rcases hK with hL | ⟨-, -, ⟨e⟩⟩
  · obtain ⟨e⟩ := PSp43.equiv_of_lieModel hL
    exact props_of_confData (PSp43.cfConfData e) c
  · exact props_of_confData (A8.cfConfData e) c

end CFSG.ComponentClassification.CatFactsSmall
