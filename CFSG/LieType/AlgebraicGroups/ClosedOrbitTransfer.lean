module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed

public noncomputable section

open WithConv TauCeti.Comodule MvPolynomial
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

attribute [local instance] TauCeti.Comodule.tensor


end CFSG.LieType.AlgebraicGroups.ClosedCone
