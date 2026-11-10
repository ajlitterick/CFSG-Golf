module

public import CFSG.Timmesfeld.Special.Commutator

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

namespace Special

theorem eq_one_of_odd_of_dvd_two_pow {n k : ℕ} (hn : Odd n) (h : n ∣ 2 ^ k) : n = 1 := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rfl
  · exact absurd hn (Nat.not_odd_iff_even.2 ((Nat.even_pow' hi.ne').2 even_two))

theorem eq_one_of_mem_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q) {g : G} (hg : g ∈ Q)
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd (orderOf_dvd_of_pow_eq_one hk'))

theorem isPGroup_closure_pair_of_orderOf {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ orderOf (x * y) = 1) :
    IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
  refine isPGroup_two_closure_pair hx hy (k := 2) ?_
  have h4 : orderOf (x * y) ∣ 2 ^ 2 := by
    rcases h with h | h | h <;> rw [h] <;> norm_num
  exact orderOf_dvd_iff_pow_eq_one.mp h4

theorem mem_centralizer_singleton {x z : G} (h : Commute x z) : x ∈ Subgroup.centralizer {z} := by
  rw [Subgroup.mem_centralizer_iff]
  rintro g rfl
  exact h.symm.eq

end Special

open Special


theorem mem_map_pCore_centralizer [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {z x : G} (hz : z ∈ D) (hx : x ∈ D) (hxz : Commute x z)
    (hmul : x * z ∈ D ∨ x = z) :
    x ∈ (CFSG.pCore 2 (Subgroup.centralizer {z})).map (Subgroup.centralizer {z}).subtype := by
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hxH : x ∈ H := by
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro g rfl
    exact hxz.symm.eq
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
  intro h
  have hhz : Commute (h : G) z := (Subgroup.mem_centralizer_iff.mp h.2 z rfl).symm
  have hcD : (h : G) * x * (h : G)⁻¹ ∈ D := conj_mem_of_isClass hclass h hx
  have h1 : (⟨x, hxH⟩ : H) * ⟨x, hxH⟩ = 1 := Subtype.ext (hD.mul_self_eq_one hx)
  have h2 : (h * ⟨x, hxH⟩ * h⁻¹) * (h * ⟨x, hxH⟩ * h⁻¹) = 1 :=
    Subtype.ext (by simpa using hD.mul_self_eq_one hcD)
  have hord : orderOf (x * ((h : G) * x * (h : G)⁻¹)) =
      orderOf ((⟨x, hxH⟩ : H) * (h * ⟨x, hxH⟩ * h⁻¹)) := by
    rw [← Subgroup.orderOf_coe]
    simp
  rcases hD.orderOf_mul hx hcD with h24 | h24 | hodd
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inl (hord ▸ h24))
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inl (hord ▸ h24)))
  by_cases h1' : orderOf (x * ((h : G) * x * (h : G)⁻¹)) = 1
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inr (hord ▸ h1')))
  exfalso
  rcases hmul with hmul | rfl
  ·
    set u := x * ((h : G) * x * (h : G)⁻¹) with hu
    have hw : (h : G) * x * (h : G)⁻¹ * z ∈ D := by
      have : (h : G) * x * (h : G)⁻¹ * z = (h : G) * (x * z) * (h : G)⁻¹ := by
        rw [mul_assoc _ (h : G)⁻¹, hhz.inv_left.eq]
        group
      rw [this]
      exact conj_mem_of_isClass hclass h hmul
    have hcomm : Commute u z :=
      hxz.mul_left ((hhz.mul_left hxz).mul_left hhz.inv_left)
    have h2u := orderOf_mul_eq_two_mul_of_odd hcomm hodd (hD.orderOf_eq_two hz)
    have heq : x * ((h : G) * x * (h : G)⁻¹ * z) = u * z := by rw [hu, ← mul_assoc]
    have hpos : 0 < orderOf u := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rcases hD.orderOf_mul hx hw with h' | h' | h' <;> rw [heq, h2u] at h'
    · omega
    · obtain ⟨k, hk⟩ := hodd
      omega
    · exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h'
  · apply h1'
    rw [hhz.eq, mul_inv_cancel_right, hD.mul_self_eq_one hx, orderOf_one]

section SpecialPair


end SpecialPair

end CFSG.Timmesfeld
