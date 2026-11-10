module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GroupActions

open scoped commutatorElement


theorem additive_scaling_commutator {R Γ : Type*} [CommRing R] [Group Γ]
    (u : Multiplicative R →* Γ) (h : Γ) (lam mu : R) (hmu : mu * (lam - 1) = 1)
    (hconj : ∀ a : R, h * u (Multiplicative.ofAdd a) * h⁻¹ = u (Multiplicative.ofAdd (lam * a)))
    (a : R) :
    u (Multiplicative.ofAdd a) =
        h * u (Multiplicative.ofAdd (mu * a)) * h⁻¹ * (u (Multiplicative.ofAdd (mu * a)))⁻¹ ∧
      u (Multiplicative.ofAdd a) ∈ commutator Γ := by
  have key : u (Multiplicative.ofAdd a) =
      h * u (Multiplicative.ofAdd (mu * a)) * h⁻¹ * (u (Multiplicative.ofAdd (mu * a)))⁻¹ := by
    rw [hconj, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    linear_combination (-a) * hmu
  refine ⟨key, ?_⟩
  rw [key, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top h) (Subgroup.mem_top _)

end CFSG.GroupActions
