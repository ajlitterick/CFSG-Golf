module

public import CFSG.Certificates.Kernel.Bounds.Co3Alt.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Co3Alt

theorem rels_eq : TauCeti.Sporadic.co3Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.co3Presentation_transcribed]
  simp [rels]

theorem gens_eq : TauCeti.Sporadic.co3Presentation.generatorCount = 7 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co3Presentation_generatorNames]


end CFSG.KBRoute.Co3Alt

end
