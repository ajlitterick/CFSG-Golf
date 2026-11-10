module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.ClassicalInvolution.Asc77

open MulAction Subgroup

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G} {A : Type*} [CommGroup A]
  (ϕ : ↥H →* A)

theorem transfer_apply_eq_one (a : G)
    (h : ∀ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H), ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ = 1) :
    MonoidHom.transfer ϕ a = 1 := by
  have := Fintype.ofFinite (Quotient (orbitRel (zpowers a) (G ⧸ H)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  exact Finset.prod_eq_one fun q _ => h _ _ _

theorem transfer_apply_eq_pow_index (a : G) (ha : a ∈ H)
    (h : ∀ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H),
      ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ = ϕ ⟨a, ha⟩ ^ n) :
    MonoidHom.transfer ϕ a = ϕ ⟨a, ha⟩ ^ H.index := by
  have := Fintype.ofFinite (Quotient (orbitRel (zpowers a) (G ⧸ H)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  calc ∏ q : Quotient (orbitRel (zpowers a) (G ⧸ H)),
        ϕ ⟨(Quotient.out q.out)⁻¹ * a ^ Function.minimalPeriod (fun x => a • x) q.out *
          Quotient.out q.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H a q.out⟩
      = ∏ q : Quotient (orbitRel (zpowers a) (G ⧸ H)),
          ϕ ⟨a, ha⟩ ^ Function.minimalPeriod (fun x => a • x) q.out :=
        Finset.prod_congr rfl fun q _ => h _ _ _
    _ = ϕ ⟨a, ha⟩ ^ ∑ q : Quotient (orbitRel (zpowers a) (G ⧸ H)),
          Function.minimalPeriod (fun x => a • x) q.out := Finset.prod_pow_eq_pow_sum _ _ _
    _ = ϕ ⟨a, ha⟩ ^ H.index := by rw [Subgroup.index_eq_sum_minimalPeriod H a]

theorem transfer_apply_ne_one (a : G) (ha : a ∈ H) (ha2 : IsPGroup 2 (zpowers a))
    (hϕ : ϕ ⟨a, ha⟩ ≠ 1) (hodd : Odd H.index)
    (h : ∀ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H),
      ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ = ϕ ⟨a, ha⟩ ^ n) :
    MonoidHom.transfer ϕ a ≠ 1 := by
  rw [transfer_apply_eq_pow_index ϕ a ha h]
  intro hpow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := ha2.exists_card_eq
  rw [Nat.card_zpowers] at hm
  have h1 : ϕ ⟨a, ha⟩ ^ 2 ^ m = 1 := by
    have : (⟨a, ha⟩ : ↥H) ^ 2 ^ m = 1 := by
      apply Subtype.ext
      rw [← hm]
      exact pow_orderOf_eq_one a
    rw [← map_pow, this, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hϕ (orderOf_eq_one_iff.mp (by simpa using hj))
  have hdvd : 2 ∣ H.index := by
    have h2 : orderOf (ϕ ⟨a, ha⟩) ∣ H.index := orderOf_dvd_of_pow_eq_one hpow
    rw [hj] at h2
    exact (dvd_pow_self 2 hj0).trans h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)


end CFSG.ClassicalInvolution.Asc77
