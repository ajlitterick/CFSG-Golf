module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Trigonalizable
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

public noncomputable section

open CategoryTheory TauCeti TauCeti.Comodule WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CommutativeReductive

universe u

section LinearAlgebra

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]


variable [PerfectField K] [FiniteDimensional K V]


end LinearAlgebra

section Restriction

variable {R : Type*} {H : Type*} {M : Type*} [CommRing R] [Semiring H] [HopfAlgebra R H]
  [Module.Flat R H] [AddCommMonoid M] [Module R M] [Comodule R H M]


end Restriction

section Regular

variable {K : Type*} {B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]


end Regular

section Jordan

variable {K : Type u} [Field K] [PerfectField K] {B : Type u} [CommRing B] [HopfAlgebra K B]


end Jordan

section Weights

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [IsReduced B] [Coalgebra.IsCocomm K B]
variable {V : Type u} [AddCommGroup V] [Module K V] [Comodule K B V] [FiniteDimensional K V]


omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] [Coalgebra.IsCocomm K B]
  [FiniteDimensional K V] in


end Weights

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]


abbrev subcomoduleAddCommGroup (N : Subcomodule K B B) : AddCommGroup N :=
  Module.addCommMonoidToAddCommGroup K

attribute [local instance] subcomoduleAddCommGroup

variable [IsReduced B] [Coalgebra.IsCocomm K B]

section Fibers

variable (N : Subcomodule K B B) [FiniteDimensional K N]

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] [Coalgebra.IsCocomm K B]
  [FiniteDimensional K N] in


variable {N} (hN : Algebra.adjoin K (N : Set B) = ⊤)
include hN


end Fibers

end Main

section CharacterKernel

variable {K : Type u} [Field K] [IsAlgClosed K]


end CharacterKernel

section Diagonalizable

attribute [local instance] subcomoduleAddCommGroup


end Diagonalizable

section Reductive


end Reductive

end CFSG.LieType.AlgebraicGroups.CommutativeReductive
