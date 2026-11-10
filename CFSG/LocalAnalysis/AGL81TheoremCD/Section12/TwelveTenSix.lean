module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNine

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem eq_seven_of_mem_sigma_of_odd_prime_divisors {M H : Subgroup G} {d : ℕ}
    (h124 : TwelveFour M H) (hd : d ∈ sigmaSet G M)
    (hJ : jSub M H = oPPrimeHull d M)
    (hprime : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (jSub M H) → q = 3 ∨ q = 7) :
    d = 7 := by
  have hdprime : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hdvdM : d ∣ Nat.card M := by
    obtain ⟨E, hEM, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hdprime.one_lt M
    have hdE : d ∣ Nat.card E := by
      have hpos : 0 < CFSG.Open.pRank d M := lt_of_lt_of_le (by norm_num) hd.2
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      refine ⟨d ^ k, ?_⟩
      rw [hEcard, hk, pow_succ]
      ring
    exact hdE.trans (Subgroup.card_dvd_of_le hEM)
  have hdvdJ : d ∣ Nat.card (jSub M H) := by
    rw [hJ]
    exact dvd_card_oPPrimeHull hdprime hdvdM
  have hdodd : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  rcases hprime d hdprime hdodd hdvdJ with h3 | h7
  · exact absurd (h3 ▸ hd) (h124 d hd).2.2
  · exact h7

theorem twelveSix_part_three_of_odd_prime_divisors {M H : Subgroup G}
    (h124 : TwelveFour M H) (hσ : (sigmaSet G M).Nonempty)
    (hJ : ∀ d ∈ sigmaSet G M, jSub M H = oPPrimeHull d M)
    (hprime : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (jSub M H) → q = 3 ∨ q = 7) :
    sigmaSet G M = {7} := by
  ext q
  constructor
  · intro hq
    exact eq_seven_of_mem_sigma_of_odd_prime_divisors h124 hq (hJ q hq) hprime
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    obtain ⟨d, hd⟩ := hσ
    rw [← eq_seven_of_mem_sigma_of_odd_prime_divisors h124 hd (hJ d hd) hprime]
    exact hd


end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
