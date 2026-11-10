module

public import CFSG.LieType.AlgebraicGroups.MaximalTorusConjugacy
public import CFSG.LieType.AlgebraicGroups.ClosedConeLimit

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone
open CFSG.LieType.AlgebraicGroups.TorusConjugacy

namespace CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar

universe u

variable {k : Type u} [Field k]

section Weight

variable {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

@[expose] def weightCoordinate (μ : M →ₐc[k] LaurentPolynomial k) :
    M →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp μ

variable (W) in
abbrev weightSpace (μ : M →ₐc[k] LaurentPolynomial k) (m : Multiplicative ℤ) : Submodule k W :=
  TauCeti.DiagonalizableGroup.weightSpace W
    (weightCoordinate μ : M →ₗc[k] MonoidAlgebra k (Multiplicative ℤ)) m


end Weight

section OrbitCone


end OrbitCone


section Normalizer


end Normalizer


end CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar
