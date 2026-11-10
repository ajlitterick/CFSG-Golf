module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

theorem exists_fixedPoint_of_involutive {X : Type*} [Finite X] (hX : Odd (Nat.card X))
    {φ : X → X} (hφ : Function.Involutive φ) : ∃ x, φ x = x := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ¬ 2 ∣ Fintype.card X := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hX)
  have hsq : (hφ.toPerm φ) ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, Equiv.Perm.mul_apply, hφ x]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) h2 hsq
  exact ⟨a, ha⟩


end CFSG.ClassicalInvolution.Asc77.AscFusion
