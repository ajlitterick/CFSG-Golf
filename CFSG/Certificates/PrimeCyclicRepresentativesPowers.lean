module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.Certificates.PrimeCyclicRepresentatives

variable {P : Type*} [Group P] [LinearOrder P]


omit [LinearOrder P] in
theorem orderOf_eq_prime_of_power (p : ℕ) (hp : p.Prime) {x : P}
    (hx : x ≠ 1) (hpow : x ^ p = 1) : orderOf x = p := by
  let : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hx


end CFSG.Certificates.PrimeCyclicRepresentatives
