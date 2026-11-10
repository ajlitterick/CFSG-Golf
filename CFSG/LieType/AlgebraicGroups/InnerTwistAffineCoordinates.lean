module

public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.LieType.AlgebraicGroups.ChevalleyLine
public import CFSG.LieType.AlgebraicGroups.ConnectedCenterAutomorphism

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u v

section PointConjugation

variable {R : Type u} [CommSemiring R]
variable {H : Type v} [CommSemiring H] [HopfAlgebra R H]


end PointConjugation

section FiniteCoordinates

variable {k : Type u} [Field k]
variable {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}


namespace SemisimpleAffineCoordinatesThree


end SemisimpleAffineCoordinatesThree

local instance (D : TauCeti.Subcoalgebra k H) : AddCommGroup D.toRegularSubcomodule :=
  Module.addCommMonoidToAddCommGroup k


end FiniteCoordinates

end CFSG.LieType.AlgebraicGroups
