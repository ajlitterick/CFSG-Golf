module

public import CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar
public import CFSG.LieType.AlgebraicGroups.TorusNormalizerOrbit
public import CFSG.LieType.AlgebraicGroups.FiniteComoduleScalarFiltration
public import CFSG.LieType.AlgebraicGroups.GradedRepresentationKernel
public import CFSG.LieType.AlgebraicGroups.ReductiveNormalUnipotent

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone
open CFSG.LieType.AlgebraicGroups.TorusConjugacy CFSG.LieType.AlgebraicGroups.RegularCocharacter
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CentralizerUnipotent

universe u

variable {k : Type u} [Field k]

section Lagrange

variable {V : Type u} [AddCommGroup V] [Module k V]


end Lagrange

section Weights

variable {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
variable (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

abbrev wt (χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) : Submodule k W :=
  TauCeti.DiagonalizableGroup.weightSpace W
    (π : M →ₗc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) χ


end Weights

section Separating

variable {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
variable (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]


variable (W) in
@[expose] def proj (S : Finset (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t₀ : kˣ)
    (χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) : Module.End k W :=
  Polynomial.aeval (basePointsRepresentation (H := M) W
      (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t₀))
    (Lagrange.basis S (fun χ => (t₀ : k) ^ ψ (Multiplicative.toAdd χ)) χ)


end Separating

section Kolchin


end Kolchin

section Main


end Main

section Reductive


end Reductive

end CFSG.LieType.AlgebraicGroups.CentralizerUnipotent
