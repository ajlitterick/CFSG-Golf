module

public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyThree

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Fi23Alt

theorem rels_eq : TauCeti.Sporadic.fi23Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.fi23Presentation_transcribed]
  simp [rels]

theorem gens_eq : TauCeti.Sporadic.fi23Presentation.generatorCount = 10 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.fi23Presentation_generatorNames]


end CFSG.KBRoute.Fi23Alt

end
