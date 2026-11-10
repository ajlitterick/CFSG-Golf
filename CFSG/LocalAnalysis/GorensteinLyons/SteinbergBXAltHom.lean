module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Module

variable (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]

@[expose] def altHom : Submodule F (Dual F V →ₗ[F] V) where
  carrier := {T | ∀ f : Dual F V, f (T f) = 0}
  add_mem' := fun {T T'} hT hT' f => by
    rw [LinearMap.add_apply, map_add, hT f, hT' f, add_zero]
  zero_mem' := fun f => by rw [LinearMap.zero_apply, map_zero]
  smul_mem' := fun c T hT f => by
    rw [LinearMap.smul_apply, map_smul, hT f, smul_zero]


section Basis


end Basis


end CFSG.LocalAnalysis.GorensteinLyons
