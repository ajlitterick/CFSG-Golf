module

public import CFSG.CGT.Stroth77.Section224Uniform
public import CFSG.CGT.Stroth77.Section33

public section

namespace CFSG.CGT.Stroth77

open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem familyOne_disjunction (τ : StrothTypeIndex) (hrel : τ.m + 1 = τ.n) :
    (∃ m : ℕ, τ = StrothTypeIndex.t100 m) ∨
    (∃ n : ℕ, τ = StrothTypeIndex.t101 n) ∨
    (∃ t : ℕ, τ = StrothTypeIndex.t110 t) ∨
    (∃ t : ℕ, τ = StrothTypeIndex.t111 t) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t120 m hm) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t121 m hm) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t130 m hm) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t131 m hm) := by
  cases τ with
  | t100 m => exact Or.inl ⟨m, rfl⟩
  | t101 s => exact Or.inr (Or.inl ⟨s, rfl⟩)
  | t110 t => exact Or.inr (Or.inr (Or.inl ⟨t, rfl⟩))
  | t111 t => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl⟩)))
  | t120 m hm =>
    right; right; right; right; left
    exact ⟨m, hm, rfl⟩
  | t121 m hm =>
    right; right; right; right; right; left
    exact ⟨m, hm, rfl⟩
  | t130 m hm =>
    right; right; right; right; right; right; left
    exact ⟨m, hm, rfl⟩
  | t131 m hm =>
    right; right; right; right; right; right; right
    exact ⟨m, hm, rfl⟩
  | t200 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type200.k] at hrel
  | t201 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type201.k] at hrel
  | t210 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type210.k] at hrel
  | t211 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type211.k] at hrel
  | t220 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type220.k] at hrel
  | t221 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type221.k] at hrel
  | t230 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type230.k] at hrel
  | t231 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type231.k] at hrel
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel


theorem commutator_zpow_eq_zpow {s d : G} (hcomm : Commute s ⁅s, d⁆) (n : ℤ) :
    ⁅s ^ n, d⁆ = ⁅s, d⁆ ^ n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using (Commute.commutatorElement_pow_left hcomm k).symm
  · have hpos : ⁅s ^ k, d⁆ = ⁅s, d⁆ ^ k := by
      simpa using (Commute.commutatorElement_pow_left hcomm k).symm
    have hcommk : Commute (s ^ k) ⁅s ^ k, d⁆ := by
      rw [hpos]
      exact (hcomm.pow_left k).pow_right k
    have hinv : ⁅(s ^ k)⁻¹, d⁆ = (⁅s ^ k, d⁆)⁻¹ := by
      rw [commutatorElement_inv_left]
      rw [show ⁅d, s ^ k⁆ = (⁅s ^ k, d⁆)⁻¹ from (commutatorElement_inv (s ^ k) d).symm]
      have hx : Commute (s ^ k) (⁅s ^ k, d⁆)⁻¹ := hcommk.inv_right
      calc (s ^ k)⁻¹ * (⁅s ^ k, d⁆)⁻¹ * s ^ k
          = (s ^ k)⁻¹ * ((⁅s ^ k, d⁆)⁻¹ * s ^ k) := by group
        _ = (s ^ k)⁻¹ * (s ^ k * (⁅s ^ k, d⁆)⁻¹) := by rw [← hx.eq]
        _ = (⁅s ^ k, d⁆)⁻¹ := by group
    rw [show s ^ (-(k : ℤ)) = (s ^ k)⁻¹ from by
      rw [_root_.zpow_neg, _root_.zpow_natCast]]
    rw [show (⁅s, d⁆ : G) ^ (-(k : ℤ)) = ((⁅s, d⁆ : G) ^ k)⁻¹ from by
      rw [_root_.zpow_neg, _root_.zpow_natCast]]
    rw [hinv, hpos]

theorem commutator_zpowers_le_of_image {s : G} {D H : Subgroup G}
    (himg : ∀ d ∈ D, ⁅s, d⁆ ∈ H)
    (hcomm : ∀ d ∈ D, Commute s ⁅s, d⁆) :
    ⁅Subgroup.zpowers s, D⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g hg d hd
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [commutator_zpow_eq_zpow (hcomm d hd) n]
  exact H.zpow_mem (himg d hd) n


theorem commutator_zpowers_le_of_pow_three_central {ρ : G} {K H : Subgroup G}
    (hconj : ∀ x ∈ K, ρ * x * ρ⁻¹ ∈ K)
    (h3 : ρ ^ 3 ∈ Subgroup.centralizer (K : Set G))
    (himg : ∀ x ∈ K, ⁅ρ, x⁆ ∈ H) :
    ⁅Subgroup.zpowers ρ, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g hg x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  let q : ℤ := n / 3
  let r : ℤ := n % 3
  have hn : n = 3 * q + r := by
    dsimp [q, r]
    exact (Int.mul_ediv_add_emod n 3).symm
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg n (by norm_num)
  have hr3 : r < 3 := by
    dsimp [r]
    exact Int.emod_lt_of_pos n (by norm_num)
  have hρn : ρ ^ n = (ρ ^ 3) ^ q * ρ ^ r := by
    rw [hn, _root_.zpow_add, _root_.zpow_mul]
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from by norm_num, _root_.zpow_natCast]
  rw [hρn, commutatorElement_mul_left_eq_conj_mul]
  have h3q_comm : Commute ((ρ ^ 3) ^ q) x := by
    have h : Commute (ρ ^ 3) x := (Subgroup.mem_centralizer_iff.mp h3 x hx).symm
    exact h.zpow_left q
  have h3q_one : ⁅(ρ ^ 3) ^ q, x⁆ = 1 := h3q_comm.commutator_eq
  rw [h3q_one, mul_one]
  have hrK : ⁅ρ ^ r, x⁆ ∈ K := by
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with h0 | h1 | h2
    · rw [h0]; simp
    · rw [h1, commutatorElement_def]
      exact K.mul_mem (by simpa using hconj x hx) (K.inv_mem hx)
    · rw [h2, show ρ ^ (2 : ℤ) = ρ * ρ from by norm_num [zpow_natCast, pow_two]]
      rw [commutatorElement_def]
      refine K.mul_mem ?_ (K.inv_mem hx)
      have h1 := hconj (ρ * x * ρ⁻¹) (hconj x hx)
      convert h1 using 1
      group
  have hcommA : Commute ((ρ ^ 3) ^ q) ⁅ρ ^ r, x⁆ := by
    have h : Commute (ρ ^ 3) ⁅ρ ^ r, x⁆ :=
      (Subgroup.mem_centralizer_iff.mp h3 _ hrK).symm
    exact h.zpow_left q
  have hconjA : (ρ ^ 3) ^ q * ⁅ρ ^ r, x⁆ * ((ρ ^ 3) ^ q)⁻¹ = ⁅ρ ^ r, x⁆ := by
    rw [hcommA.eq]
    group
  rw [hconjA]
  have hrH : ⁅ρ ^ r, x⁆ ∈ H := by
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with h0 | h1 | h2
    · rw [h0]; simp
    · rw [h1]; simpa using himg x hx
    · rw [h2, show ρ ^ (2 : ℤ) = ρ * ρ from by norm_num [zpow_natCast, pow_two]]
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hconj_eq : ρ * ⁅ρ, x⁆ * ρ⁻¹ = ⁅ρ, ρ * x * ρ⁻¹⁆ := by
        rw [conjugate_commutatorElement]
        congr 1 <;> group
      rw [hconj_eq]
      exact H.mul_mem (by simpa using himg _ (hconj x hx)) (by simpa using himg x hx)
  exact hrH


end CFSG.CGT.Stroth77

end
