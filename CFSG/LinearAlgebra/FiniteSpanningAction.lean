module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.LinearAlgebra.Span.Basic

public noncomputable section

open scoped Pointwise

namespace CFSG.Certificates

variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

@[expose] def linearSetRestriction (X : Set V) :
    MulAction.stabilizer (V ≃ₗ[K] V) X →* Equiv.Perm X :=
  MulAction.toPermHom _ _

theorem linearSetRestriction_injective (X : Set V)
    (hspan : Submodule.span K X = ⊤) : Function.Injective (linearSetRestriction (K := K) X) := by
  intro f g h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on hspan
  intro x hx
  exact congrArg (fun e : Equiv.Perm X => (e ⟨x, hx⟩ : V)) h

end CFSG.Certificates

namespace CFSG.LinearAlgebra


end CFSG.LinearAlgebra
