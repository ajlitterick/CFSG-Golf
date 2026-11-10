module

public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension
public import CFSG.LieType.AlgebraicGroups.DynamicUnipotentDerived
public import Mathlib.Algebra.Module.Submodule.Union

public noncomputable section

open WithConv
open TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.RegularCocharacter

universe u

variable {k : Type u} [Field k]


@[expose] noncomputable def additiveToLaurentBialg :
    MonoidAlgebra k (Multiplicative ℤ) →ₐc[k] LaurentPolynomial k :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm.toBialgHom


@[expose] noncomputable def cocharacterOfAddHom {n : ℕ}
    (ψ₀ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ)
    {M : Type u} [CommRing M] [HopfAlgebra k M]
    (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) :
    M →ₐc[k] LaurentPolynomial k :=
  additiveToLaurentBialg.comp ((MonoidAlgebra.mapDomainBialgHom k
    (AddMonoidHom.toMultiplicative ψ₀)).comp π)


section Separating


end Separating


section SplitCoordinates


end SplitCoordinates


end CFSG.LieType.AlgebraicGroups.RegularCocharacter
