module

public import CFSG.LieType.AlgebraicGroups.ImagePointsOpen
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import CFSG.LieType.AlgebraicGroups.ClosedCone

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {M : Type w} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]


section Domain

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]

instance isDomain_tensorPolynomial : IsDomain (H ⊗[k] Polynomial k) :=
  Function.Injective.isDomain ((polyEquivTensor k H).symm : H ⊗[k] Polynomial k →+* Polynomial H)
    (polyEquivTensor k H).symm.injective

instance finiteType_tensorPolynomial : Algebra.FiniteType k (H ⊗[k] Polynomial k) :=
  Algebra.FiniteType.equiv (Algebra.FiniteType.trans (S := H) inferInstance inferInstance)
    (polyEquivTensor k H)


end Domain

end CFSG.LieType.AlgebraicGroups.ClosedCone
