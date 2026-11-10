module

public import CFSG.Assembly.OrderReductions.ThompsonCharacteristic
public import CFSG.Assembly.OrderReductions.QuadraticPrimeOrder
public import CFSG.Assembly.OrderReductions.ThompsonQuotient

public section

namespace CFSG.OrderReductions.ThompsonQuotientCharacteristic

open CFSG.OrderReductions.ThompsonCenter CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore
open CFSG.OrderReductions.PrimeComplementCore CFSG.OrderReductions.ThompsonCoreProduct

theorem coreProduct_characteristic_of_quotient_stability {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (sylow : Sylow prime group)
    (stable : ∀ normal : Subgroup (group ⧸ primeComplementCore prime group), ∀ [normal.Normal],
      IsPGroup prime normal → primeStable prime (conjugationAction normal)) :
    (coreProduct prime sylow).Characteristic := by
  apply CFSG.OrderReductions.ThompsonQuotient.coreProduct_characteristic_of_quotient_center
  let core := primeComplementCore prime group
  let image := sylow.mapSurjective (QuotientGroup.mk'_surjective core)
  have characteristic := CFSG.OrderReductions.ThompsonCharacteristic.glauberman_characteristic prime odd_prime image
    (CFSG.OrderReductions.SolvablePrimeCore.quotient_centralizer_primeCore_le prime) stable
  rw [Sylow.coe_mapSurjective] at characteristic
  exact characteristic


end CFSG.OrderReductions.ThompsonQuotientCharacteristic
