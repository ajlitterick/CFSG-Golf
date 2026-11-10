module

public import CFSG.Certificates.PrimeCyclicRepresentativesPowers

public section

namespace CFSG.Certificates.PrimeCyclicRepresentatives

variable {P : Type*} [Group P] [LinearOrder P]


omit [LinearOrder P] in
theorem orderOf_and_zpowers_eq_of_mem_prime_subgroup (p : ℕ) (hp : p.Prime)
    (Q : Subgroup P) (hQ : Nat.card Q = p) {x : P} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    orderOf x = p ∧ Subgroup.zpowers x = Q := by
  have hpow : x ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (by simpa only [hQ] using Q.orderOf_dvd_natCard hx)
  have horder := orderOf_eq_prime_of_power p hp hx1 hpow
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact hp.ne_zero)
  refine ⟨horder, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_⟩
  rw [Nat.card_zpowers, horder, hQ]


section Finite


end Finite

end PrimeCyclicRepresentatives

open PrimeCyclicRepresentatives


end CFSG.Certificates
