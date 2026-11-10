module

public import CFSG.Certificates.Kernel.Orders.Co1.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.H
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.One
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OrdCo1

@[expose] def nGens : Nat := 8

theorem gens_eq : TauCeti.Sporadic.co1Presentation.generatorCount = nGens := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co1Presentation_generatorNames, nGens]


end CFSG.KD.OrdCo1

end
