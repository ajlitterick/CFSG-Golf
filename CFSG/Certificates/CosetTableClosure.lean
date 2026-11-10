module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

theorem invCode_two_mul (i : ℕ) : invCode (2 * i) = 2 * i + 1 := by
  have h : Nat.beq (Nat.mod (2 * i) 2) 0 = true := by
    rw [Nat.beq_eq]
    exact Nat.mul_mod_right 2 i
  rw [invCode, h]
  rfl

theorem invCode_two_mul_add_one (i : ℕ) : invCode (2 * i + 1) = 2 * i := by
  have h : Nat.beq (Nat.mod (2 * i + 1) 2) 0 = false := by
    cases hb : Nat.beq (Nat.mod (2 * i + 1) 2) 0 with
    | false => rfl
    | true =>
      rw [Nat.beq_eq] at hb
      have : (2 * i + 1) % 2 = 1 := by omega
      exact absurd hb (by rw [show Nat.mod (2 * i + 1) 2 = (2 * i + 1) % 2 from rfl, this]; simp)
  rw [invCode, h]
  rfl

section Closure


end Closure

end CFSG.CosetTable
