module

public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.FixedProduct

open CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k]

instance tensorProductFiniteType (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k) :
    Algebra.FiniteType k (T ⊗[k] S) :=
  TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) T S

section Definitions


end Definitions

section Norm


end Norm

section TorusWrapper


end TorusWrapper

end CFSG.LieType.AlgebraicGroups.FixedProduct
