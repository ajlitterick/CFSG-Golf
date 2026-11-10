module

public import CFSG.Certificates.Kernel.Orders.Co3.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.H
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.OrdCo3

@[expose] def nGens : Nat := 7

theorem gens_eq : TauCeti.Sporadic.co3Presentation.generatorCount = nGens := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co3Presentation_generatorNames, nGens]


end CFSG.KD.OrdCo3

end
