module

public import CFSG.Quasithin.Background.C116Two.NatLin2Defs

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

theorem charP_two_of_card {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨p, hc⟩ := CharP.exists F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F p
  have hdvd : p ∣ 2 ^ n := by
    rw [← hcard, hm]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc


end CFSG.Quasithin.C116Two
