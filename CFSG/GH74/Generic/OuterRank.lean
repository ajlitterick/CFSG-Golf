module

public import CFSG.GH74.Generic.QuaternionCentral

public section

namespace CFSG.GH74.Generic

open Subgroup

theorem isPGroup_zpowers_of_pow_two_pow_eq_one {X : Type*} [Group X] {v : X} {n : ℕ}
    (h : v ^ (2 ^ n) = 1) : IsPGroup 2 (Subgroup.zpowers v) := by
  have hord : orderOf v ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])


end CFSG.GH74.Generic
