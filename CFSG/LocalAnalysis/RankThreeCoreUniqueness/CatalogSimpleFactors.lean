module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralCoreReduction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MinimalNormalFactors
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CatalogSections

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem characteristically_simple_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hcharacteristic : ∀ subgroup : Subgroup G, subgroup.Characteristic →
      subgroup = ⊥ ∨ subgroup = ⊤)
    (prime : ℕ) (hprime : prime.Prime) (hdivides : prime ∣ Nat.card G) :
    primeComplementCore (G := G) prime = ⊥ := by
  rcases hcharacteristic (primeComplementCore prime)
      (primeComplementCore_characteristic prime) with hbottom | htop
  · exact hbottom
  · have hcoprime := primeComplementCore_coprime (G := G) prime
    rw [htop, Subgroup.card_top] at hcoprime
    exact False.elim ((hprime.coprime_iff_not_dvd.mp hcoprime) hdivides)

theorem characteristically_simple_normal_factor_prime_dvd
    {G : Type*} [Group G] [Finite G]
    (hcharacteristic : ∀ subgroup : Subgroup G, subgroup.Characteristic →
      subgroup = ⊥ ∨ subgroup = ⊤)
    (prime : ℕ) (hprime : prime.Prime) (hdivides : prime ∣ Nat.card G)
    (normalFactor : Subgroup G) (hnormal : normalFactor.Normal)
    (hnontrivial : normalFactor ≠ ⊥) : prime ∣ Nat.card normalFactor := by
  by_contra hnotDivides
  have hbound := normal_coprime_le_primeComplementCore prime normalFactor hnormal
    (hprime.coprime_iff_not_dvd.mpr hnotDivides)
  rw [characteristically_simple_primeComplementCore_eq_bot
    hcharacteristic prime hprime hdivides] at hbound
  exact hnontrivial (le_bot_iff.mp hbound)


end CFSG.RankThreeCoreUniqueness.Helpers
