module

public import CFSG.Certificates.Kernel.Orders.Ru.Checks.R
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.H
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OrdRu

@[expose] def nGens : Nat := 3

theorem gens_eq : TauCeti.Sporadic.ruPresentation.generatorCount = nGens := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.ruPresentation_generatorNames, nGens]


end CFSG.KD.OrdRu

end
