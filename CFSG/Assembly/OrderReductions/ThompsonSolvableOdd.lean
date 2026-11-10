module

public import CFSG.Assembly.OrderReductions.SolvableOddStability
public import CFSG.Assembly.OrderReductions.ThompsonQuotientCharacteristic

public section

namespace CFSG.OrderReductions.ThompsonSolvableOdd

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeComplementCore CFSG.OrderReductions.ThompsonCoreProduct
open CFSG.OrderReductions.ThompsonCenter


theorem coreProduct_characteristic_of_solvable_odd {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (odd_order : Odd (Nat.card group)) (sylow : Sylow prime group) :
    (coreProduct prime sylow).Characteristic := by
  apply CFSG.OrderReductions.ThompsonQuotientCharacteristic.coreProduct_characteristic_of_quotient_stability
    prime odd_prime sylow
  intro normal normal_instance prime_normal
  exact CFSG.OrderReductions.SolvableOddStability.primeStable_of_solvable_odd prime prime_normal (conjugationAction normal)
    (odd_order.of_dvd_nat (Subgroup.card_quotient_dvd_card (primeComplementCore prime group)))

theorem coreProduct_independent_of_solvable_odd {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (odd_order : Odd (Nat.card group)) (sylow : Sylow prime group) :
    ∀ other : Sylow prime group, coreProduct prime other = coreProduct prime sylow :=
  independent_sylow_of_coreProduct_characteristic prime sylow
    (coreProduct_characteristic_of_solvable_odd prime odd_prime odd_order sylow)

end CFSG.OrderReductions.ThompsonSolvableOdd
