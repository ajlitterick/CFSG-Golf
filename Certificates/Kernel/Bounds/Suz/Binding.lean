module

public import Certificates.Kernel.Bounds.Suz.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import Std.Tactic.BVDecide.Normalize.Bool

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Suz

theorem rels_eq : TauCeti.Sporadic.suzPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.suzPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem gens_eq : TauCeti.Sporadic.suzPresentation.generatorCount = 7 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.suzPresentation_generatorNames]


end CFSG.KBRoute.Suz

end
