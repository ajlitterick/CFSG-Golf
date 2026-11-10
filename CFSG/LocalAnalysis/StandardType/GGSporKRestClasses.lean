module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverSpec

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_cover_of_classes {K : Type} [Group K] {p : ℕ} (hp : p.Prime) (reps : List K)
    (hcomplete : ∀ s : K, orderOf s = p → ∃ r ∈ reps, IsConj r s)
    (hgen : ∀ r ∈ reps, ∀ x : K, IsConj r x → SporKRestGenerating p x) : SporKRestCover p K := by
  intro E hE hcard
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hlt : 1 < Nat.card E := by
    rw [hcard]
    nlinarith [hp.two_le]
  have hbot : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp hlt
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hbot
  obtain ⟨x, hxE, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial E
  have hpow : x ^ p = 1 := hE.2 x hxE
  have hord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  obtain ⟨r, hr, hrx⟩ := hcomplete x hord
  exact ⟨x, hxE, hx1, hgen r hr x hrx⟩


end CFSG.StandardType.SporadicShape
