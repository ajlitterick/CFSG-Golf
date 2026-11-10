module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Data.Set.Image
public import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.EPilot

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_eq_conj_of_inv_mul_mem {Q : Subgroup G} (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {m m' : G} (h : m⁻¹ * m' ∈ Q) {x : G} (hx : x ∈ Q) : m' * x * m'⁻¹ = m * x * m⁻¹ := by
  have hc := hQ _ h x hx
  calc m' * x * m'⁻¹ = m * ((m⁻¹ * m') * x) * (m⁻¹ * m')⁻¹ * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * m')) * (m⁻¹ * m')⁻¹ * m⁻¹ := by rw [hc]
    _ = m * x * m⁻¹ := by group


end CFSG.SeitzReduction.EPilot
