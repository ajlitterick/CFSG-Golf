module

public import CFSG.LieType.AlgebraicGroups.CartanCentralizer
public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed

public noncomputable section

open WithConv TauCeti TauCeti.Comodule CategoryTheory
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CentralTorus

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]


section Tools


end Tools


section Induction


attribute [local instance] TauCeti.Comodule.tensor TauCeti.Comodule.dual


end Induction

end CFSG.LieType.AlgebraicGroups.CentralTorus

namespace CFSG.LieType.AlgebraicGroups.CartanComponent

universe u


end CFSG.LieType.AlgebraicGroups.CartanComponent
