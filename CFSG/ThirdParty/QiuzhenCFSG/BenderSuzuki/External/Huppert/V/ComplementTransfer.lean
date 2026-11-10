module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.SamePrime

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v


public theorem hkt_exists_prime_dvd_ne_of_not_prime_power {m p : ℕ}
    (hm0 : m ≠ 0) (hm_not : ∀ n, m ≠ p ^ n) :
    ∃ q, Nat.Prime q ∧ q ∣ m ∧ q ≠ p := by
  by_contra! h
  have h' : ∀ {d}, Nat.Prime d → d ∣ m → d = p := by
    intro d hprime hdvd
    exact h d hprime hdvd
  apply hm_not (Nat.primeFactorsList m).length
  exact Nat.eq_prime_pow_of_unique_prime_dvd hm0 h'


end External
end CFSG.BenderSuzuki
