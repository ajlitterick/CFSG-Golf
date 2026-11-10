module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SimsG4
section Sp

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def spGroup (B : LinearMap.BilinForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' := fun {g h} hg hh x y => by
    change B (g (h x)) (g (h y)) = B x y
    rw [hg, hh]
  one_mem' := fun x y => rfl
  inv_mem' := fun {g} hg x y => by
    have := hg (g⁻¹ x) (g⁻¹ y)
    simpa using this.symm


@[expose] def IsTransv (g : V ≃ₗ[F] V) : Prop :=
  Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) = 1 ∧
    ((g : V →ₗ[F] V) - LinearMap.id) ∘ₗ ((g : V →ₗ[F] V) - LinearMap.id) = 0

@[expose] def commSpace (g : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)


@[expose] def twoPrimeResidual (H : Type*) [Group H] : Subgroup H :=
  sInf {N : Subgroup H | N.Normal ∧ Odd N.index}

@[expose] def twoPrimeResidualOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (twoPrimeResidual ↥H).map H.subtype

@[expose] def transvSet (G₀ : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V) :=
  {d | d ∈ G₀ ∧ IsTransv d}

@[expose] def transvGen (G₀ : Subgroup (V ≃ₗ[F] V)) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure (transvSet G₀)


@[expose] def IsIrredOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∀ W : Submodule F V, (∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def IsImprimitiveOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ (r : ℕ) (W : Fin r → Submodule F V), 1 < r ∧ (∀ i, W i ≠ ⊥) ∧ iSupIndep W ∧
    (⨆ i, W i) = ⊤ ∧ ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j


@[expose] def xHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {e | e ∈ spGroup B ∧ IsTransv e ∧ e * d = d * e}


@[expose] def IsNondegLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0


end Sp

section Orth

variable (K : Type) [Field K]

@[expose] def isometryGroup (q : (Fin 4 → K) → K) : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) where
  carrier := {M | ∀ v, q ((M : Matrix (Fin 4) (Fin 4) K).mulVec v) = q v}
  mul_mem' := fun {M N} hM hN v => by
    have h1 := hM ((N : Matrix (Fin 4) (Fin 4) K).mulVec v)
    have h2 := hN v
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1 ⊢
    rw [h1, h2]
  one_mem' := fun v => by simp
  inv_mem' := fun {M} hM v => by
    have h := hM (((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v)
    rw [Matrix.mulVec_mulVec] at h
    have h2 : ((M : Matrix (Fin 4) (Fin 4) K) *
        ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, Matrix.one_mulVec] at h
    exact h.symm


end Orth

section Cases


end Cases

end CFSG.Quasithin.SimsG4
