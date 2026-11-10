module

public import CFSG.LinearAlgebra.SteinbergBQShearGroup
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


@[expose] def fixedSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Λ : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W where
  carrier := {z | ∀ μ ∈ Λ, μ z = z}
  add_mem' {z z'} hz hz' μ hμ := by rw [map_add, hz μ hμ, hz' μ hμ]
  zero_mem' μ _ := map_zero μ
  smul_mem' c z hz μ hμ := by rw [map_smul, hz μ hμ]

theorem mem_fixedSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {Λ : Subgroup (W ≃ₗ[ZMod 2] W)} {z : W} : z ∈ fixedSub Λ ↔ ∀ μ ∈ Λ, μ z = z :=
  Iff.rfl

end CFSG.LinearAlgebra.SteinbergBQ

