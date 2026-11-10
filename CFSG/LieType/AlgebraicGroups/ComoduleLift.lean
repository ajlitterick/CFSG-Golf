module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

section Tensor

attribute [local instance] TauCeti.Comodule.tensor

variable {M E : Type u} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]
  [AddCommGroup E] [Module k E] [TauCeti.Comodule k H E]

end Tensor

section Exterior

attribute [local instance] TauCeti.Comodule.exteriorAlgebra

variable {M : Type u} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]


end Exterior

section Regular

@[expose] def restrictSubcomodule (V : TauCeti.Subcomodule k H H) (φ : H →ₐc[k] H)
    (hφV : ∀ v ∈ V, φ v ∈ V) : V →ₗ[k] V where
  toFun v := ⟨φ v, hφV v v.2⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)

@[simp]
theorem coe_restrictSubcomodule (V : TauCeti.Subcomodule k H H) (φ : H →ₐc[k] H)
    (hφV : ∀ v ∈ V, φ v ∈ V) (v : V) :
    (restrictSubcomodule V φ hφV v : H) = φ v :=
  rfl

@[expose] def restrictSubcomoduleEquiv (V : TauCeti.Subcomodule k H H) (φ ψ : H →ₐc[k] H)
    (hψφ : (ψ : H →ₐ[k] H).comp (φ : H →ₐ[k] H) = AlgHom.id k H)
    (hφψ : (φ : H →ₐ[k] H).comp (ψ : H →ₐ[k] H) = AlgHom.id k H)
    (hφV : ∀ v ∈ V, φ v ∈ V) (hψV : ∀ v ∈ V, ψ v ∈ V) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (restrictSubcomodule V φ hφV) (restrictSubcomodule V ψ hψV)
    (LinearMap.ext fun v => Subtype.ext (AlgHom.congr_fun hφψ v))
    (LinearMap.ext fun v => Subtype.ext (AlgHom.congr_fun hψφ v))

@[simp]
theorem coe_restrictSubcomoduleEquiv (V : TauCeti.Subcomodule k H H) (φ ψ : H →ₐc[k] H)
    (hψφ : (ψ : H →ₐ[k] H).comp (φ : H →ₐ[k] H) = AlgHom.id k H)
    (hφψ : (φ : H →ₐ[k] H).comp (ψ : H →ₐ[k] H) = AlgHom.id k H)
    (hφV : ∀ v ∈ V, φ v ∈ V) (hψV : ∀ v ∈ V, ψ v ∈ V) (v : V) :
    (restrictSubcomoduleEquiv V φ ψ hψφ hφψ hφV hψV v : H) = φ v :=
  rfl

end Regular

end CFSG.LieType.AlgebraicGroups.ClosedCone
