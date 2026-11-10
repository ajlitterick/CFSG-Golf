module

public import CFSG.CharacterTheory.Semidihedral.Local.CentralizerOddCoreAction
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GroupTheory

open SemidirectProduct

universe u

variable {G P : Type*} [Group G] [Group P]

@[expose] def actionPCore (p : ℕ) (ρ : G →* MulAut P) : Subgroup G :=
  (CFSG.pCore p (G ⧸ ρ.ker)).comap (QuotientGroup.mk' ρ.ker)

@[expose] def actionCommutator (ρ : G →* MulAut P) (u : P) (x : G) : P ⋊[ρ] G :=
  (inl u)⁻¹ * (inr x)⁻¹ * inl u * inr x

@[expose] def IsPStableAction (p : ℕ) (ρ : G →* MulAut P) : Prop :=
  ∀ x : G, (∀ u : P, (actionCommutator ρ u x)⁻¹ * (inr x)⁻¹ * actionCommutator ρ u x * inr x = 1) →
    x ∈ actionPCore p ρ

theorem inr_inv_mul_inl_mul_inr (ρ : G →* MulAut P) (u : P) (x : G) :
    ((inr x)⁻¹ * inl u * inr x : P ⋊[ρ] G) = inl (ρ x⁻¹ u) := by
  rw [inl_aut, ← map_inv, inv_inv]

theorem actionCommutator_eq (ρ : G →* MulAut P) (u : P) (x : G) :
    actionCommutator ρ u x = inl (u⁻¹ * ρ x⁻¹ u) := by
  rw [actionCommutator, mul_assoc, mul_assoc, ← mul_assoc (inr x)⁻¹,
    inr_inv_mul_inl_mul_inr, ← map_inv, ← map_mul]

theorem double_commutator_eq_one_iff (ρ : G →* MulAut P) (u : P) (x : G) :
    (actionCommutator ρ u x)⁻¹ * (inr x)⁻¹ * actionCommutator ρ u x * inr x = 1 ↔
      ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u := by
  rw [actionCommutator_eq, mul_assoc, mul_assoc, ← mul_assoc (inr x)⁻¹,
    inr_inv_mul_inl_mul_inr, ← map_inv, ← map_mul, ← map_one (inl : P →* P ⋊[ρ] G),
    inl_injective.eq_iff, inv_mul_eq_one, eq_comm]


end CFSG.GroupTheory
