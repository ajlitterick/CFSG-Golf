module

public import CFSG.LieType.AlgebraicGroups.ComoduleLift
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Subspace
public import CFSG.Mathlib.LinearAlgebra.ExteriorLieStabilizer
public import CFSG.LieType.AlgebraicGroups.ChevalleyTangent
public import CFSG.ThirdParty.TauCeti.ExteriorDifferential

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {M : Type u} [AddCommGroup M] [Module k M]

section Linear


end Linear

section Points

attribute [local instance] TauCeti.Comodule.exteriorAlgebra

variable {H : Type u} [CommRing H] [HopfAlgebra k H] [TauCeti.Comodule k H M]


end Points

section Hopf

attribute [local instance] TauCeti.Comodule.exteriorAlgebra


end Hopf

end CFSG.LieType.AlgebraicGroups.ClosedCone
