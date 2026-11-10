module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace LinearDegree

open Matrix

theorem pow_card_eq_zero_of_isNilpotent {k : Type*} [Field k] {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n k} (hM : IsNilpotent M) : M ^ Fintype.card n = 0 := by
  have h2 : M.charpoly = Polynomial.X ^ Fintype.card n := by
    rw [← sub_eq_zero]
    exact (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero
  have := Matrix.aeval_self_charpoly M
  rw [h2] at this
  simpa using this

theorem pow_two_pow_eq_one_of_le {k : Type*} [Field k] [CharP k 2] {d : ℕ} (hd : 1 ≤ d)
    {x : GL (Fin d) k} {a : ℕ} (hx : x ^ (2 ^ a) = 1) {j : ℕ} (hj : d ≤ 2 ^ j) :
    x ^ (2 ^ j) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set X : Matrix (Fin d) (Fin d) k := (x : Matrix (Fin d) (Fin d) k)
  have hX : X ^ (2 ^ a) = 1 := by
    have := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k)) hx
    simpa [X] using this
  have hnil : IsNilpotent (X - 1) := by
    refine ⟨2 ^ a, ?_⟩
    rw [sub_pow_char_pow_of_commute 2 a (Commute.one_right X), hX, one_pow, sub_self]
  have hd' := pow_card_eq_zero_of_isNilpotent hnil
  rw [Fintype.card_fin] at hd'
  have h0 : (X - 1) ^ (2 ^ j) = 0 := by
    rw [← Nat.sub_add_cancel hj, pow_add, hd', mul_zero]
  rw [sub_pow_char_pow_of_commute 2 j (Commute.one_right X), one_pow, sub_eq_zero] at h0
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact h0

end LinearDegree

open LinearDegree


end CFSG.ComponentClassification.UnbalancedGS
