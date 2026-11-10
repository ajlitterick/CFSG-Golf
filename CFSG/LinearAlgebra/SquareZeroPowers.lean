module

public import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Ring.Defs

public section

namespace CFSG.LinearGroups

theorem one_add_pow_of_sq_eq_zero {R : Type*} [Ring R] {N : R} (hN : N ^ 2 = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : R) * N := by
  have hNN : N * N = 0 := by rw [← sq]; exact hN
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    calc (1 + (k : R) * N) * (1 + N) = 1 + ((k : R) + 1) * N + (k : R) * (N * N) := by
          noncomm_ring
      _ = 1 + ((k : R) + 1) * N := by rw [hNN, mul_zero, add_zero]


end CFSG.LinearGroups
