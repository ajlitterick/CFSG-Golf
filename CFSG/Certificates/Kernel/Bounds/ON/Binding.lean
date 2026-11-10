module

public import CFSG.Certificates.Kernel.Bounds.ON.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
public import Std.Tactic.BVDecide.Normalize.Bool

open CFSG.Certificates

public section

namespace CFSG.KBRoute.ON

theorem rels_eq : TauCeti.Sporadic.onanPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.onanPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem gens_eq : TauCeti.Sporadic.onanPresentation.generatorCount = 7 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.onanPresentation_generatorNames]


end CFSG.KBRoute.ON

end
