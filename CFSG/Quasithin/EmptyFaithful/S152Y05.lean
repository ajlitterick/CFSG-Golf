module

public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.Quasithin

open CFSG.OddInversion
open scoped commutatorElement Pointwise

variable {A : Type*} [Group A]

theorem eq_one_of_sq_eq_one_of_odd_card {H : Type*} [Group H] [Finite H] (hH : Odd (Nat.card H))
    {g : H} (hg : g ^ 2 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  have h2 : Odd (orderOf g) := Odd.of_dvd_nat hH (orderOf_dvd_natCard g)
  have : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  exact orderOf_eq_one_iff.mp this


end CFSG.Quasithin
