module

public import CFSG.Certificates.Kernel.Bounds.M23.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyThree
public import Std.Tactic.BVDecide.Normalize.Bool

open CFSG.Certificates

public section

namespace CFSG.KBRoute.M23

theorem rels_eq : TauCeti.Sporadic.m23Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.m23Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem gens_eq : TauCeti.Sporadic.m23Presentation.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.m23Presentation_generatorNames]


end CFSG.KBRoute.M23

end
