module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionPlaneGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w


theorem subgroup_eq_top_of_contains_sylows {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G)
    (hcontains : ∀ prime : ℕ, prime.Prime → ∃ sylow : Sylow prime G, (sylow : Subgroup G) ≤ subgroup) :
    subgroup = ⊤ := by
  apply Subgroup.index_eq_one.mp
  by_contra hne
  obtain ⟨prime, hprime, hdiv⟩ := Nat.exists_prime_and_dvd hne
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨sylow, hle⟩ := hcontains prime hprime
  exact sylow.not_dvd_index (hdiv.trans (Subgroup.index_dvd_of_le hle))


end CFSG.RankThreeEvenClassification.Helpers
