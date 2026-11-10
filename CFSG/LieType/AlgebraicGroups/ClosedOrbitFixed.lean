module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitCone
public import CFSG.LieType.AlgebraicGroups.ConeIncidence
public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupComponent
public import CFSG.Mathlib.RingTheory.KrullDimensionComparison
public import TauCeti.Algebra.Coalgebra.Comodule.Product

public noncomputable section

open WithConv TauCeti.Comodule MvPolynomial
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

section Coordinates

variable {M W : Type u} [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W]


end Coordinates

section Kernel

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {M : Type u} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]


end Kernel

section Tensor

attribute [local instance] TauCeti.Comodule.tensor

variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]


end Tensor


section Contraction

attribute [local instance] TauCeti.Comodule.tensor

variable {W F : Type u} [AddCommGroup W] [Module k W] [AddCommGroup F] [Module k F]

@[expose] def contract (φ : Module.Dual k F) : W ⊗[k] F →ₗ[k] W :=
  (TensorProduct.rid k W).toLinearMap ∘ₗ LinearMap.lTensor W φ

@[simp]
theorem contract_tmul (φ : Module.Dual k F) (w : W) (f : F) :
    contract φ (w ⊗ₜ f) = φ f • w := by
  simp [contract]


end Contraction


section Diagonal

attribute [local instance] TauCeti.Comodule.tensor

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]


end Diagonal


section Dimension

attribute [local instance] TauCeti.Comodule.tensor

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]


end Dimension

section Closed

attribute [local instance] TauCeti.Comodule.tensor

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]


end Closed


section Ratio

variable [IsAlgClosed k]
variable {M W : Type u} [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W]


end Ratio

section Fixed

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]


attribute [local instance] TauCeti.Comodule.tensor


end Fixed

end CFSG.LieType.AlgebraicGroups.ClosedCone
