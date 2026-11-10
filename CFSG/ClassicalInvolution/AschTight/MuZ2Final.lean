module

public import CFSG.ClassicalInvolution.AschTight.MuZ2Closed
public import CFSG.ClassicalInvolution.AschTight.CSMD
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem odd_geom_sum {u : ℤ} (hu : Odd u) {m : ℕ} (hm : Odd m) :
    Odd (∑ i ∈ Finset.range m, u ^ i) := by
  have key : ∀ n : ℕ, (Odd (∑ i ∈ Finset.range n, u ^ i) ↔ Odd n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : ¬ Even (u ^ n) := Int.not_even_iff_odd.mpr hu.pow
      rw [Finset.sum_range_succ, Int.odd_add, ih, Nat.odd_add_one]
      simp [hne]
  exact (key m).mpr hm

theorem isCoprime_two_pow_of_odd {c : ℤ} (hc : Odd c) (e : ℕ) : IsCoprime ((2 : ℤ) ^ e) c := by
  obtain ⟨c', rfl⟩ := hc
  exact IsCoprime.pow_left ⟨-c', 1, by ring⟩

namespace SDData

variable {P : Subgroup G} {a b : G} {M : ℕ}

theorem mem_centralizer_of_odd [Finite G] (h : SDData P a b M) {n : G}
    (hnN : n ∈ Subgroup.normalizer (P : Set G)) (hn : Odd (orderOf n)) :
    n ∈ Subgroup.centralizer (P : Set G) := by
  have hM := h.M_pos
  obtain ⟨e, he⟩ := h.pow2
  have h8 : (8 * M : ℤ) = 2 ^ (e + 3) := by rw [he]; push_cast; ring
  set m := orderOf n with hm
  have hnm : n ^ m = 1 := pow_orderOf_eq_one n
  have hconjP : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hnN x).mp hx
  obtain ⟨u, hu⟩ : ∃ u : ℤ, a ^ u = n * a * n⁻¹ := by
    rcases h.mem_or (hconjP a h.a_mem) with hu | ⟨i, hi⟩
    · exact hu
    · exfalso
      have hord : orderOf (n * a * n⁻¹) = 8 * M := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.ord]
      have hdvd : orderOf (n * a * n⁻¹) ∣ 4 := by
        rw [← hi]
        exact orderOf_dvd_of_pow_eq_one (h.pow_four i)
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  have hσ : ∀ k : ℕ, n ^ k * a * (n ^ k)⁻¹ = a ^ (u ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc n ^ (k + 1) * a * (n ^ (k + 1))⁻¹ = n * (n ^ k * a * (n ^ k)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = a ^ (u ^ (k + 1)) := by
            rw [ih, ← _root_.conj_zpow, ← hu, ← zpow_mul, pow_succ']
  have hu1 : n * a * n⁻¹ = a := by
    have h1 := hσ m
    rw [hnm, one_mul, inv_one, mul_one] at h1
    have h2 : (8 * M : ℤ) ∣ u ^ m - 1 := by
      rw [← h.zpow_eq_one_iff, zpow_sub, zpow_one, ← h1, mul_inv_cancel]
    have hu_odd : Odd u := by
      rcases Int.even_or_odd u with hev | hodd
      · exfalso
        have h3 : (2 : ℤ) ∣ u ^ m - 1 := dvd_trans ⟨4 * M, by ring⟩ h2
        have h4 : (2 : ℤ) ∣ u ^ m := dvd_pow (even_iff_two_dvd.mp hev) hn.pos.ne'
        have h5 := dvd_sub h4 h3
        simp at h5
      · exact hodd
    have hcop : IsCoprime (8 * M : ℤ) (∑ i ∈ Finset.range m, u ^ i) := by
      rw [h8]; exact isCoprime_two_pow_of_odd (odd_geom_sum hu_odd hn) _
    have h3 : (8 * M : ℤ) ∣ (∑ i ∈ Finset.range m, u ^ i) * (u - 1) := by
      rw [geom_sum_mul]; exact h2
    have h4 := hcop.dvd_of_dvd_mul_left h3
    rw [← hu]
    calc a ^ u = a ^ (u - 1) * a := by rw [← zpow_add_one, sub_add_cancel]
      _ = a := by rw [(h.zpow_eq_one_iff _).mpr h4, one_mul]
  have hinv : n⁻¹ * a * n = a := by
    calc n⁻¹ * a * n = n⁻¹ * (n * a * n⁻¹) * n := by rw [hu1]
      _ = a := by group
  have hconjinv : ∀ i : ℤ, n⁻¹ * a ^ i * n = a ^ i := by
    intro i
    have := map_zpow (MulAut.conj n⁻¹) a i
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hinv]
  obtain ⟨v, hv⟩ : ∃ v : ℤ, a ^ v * b = n * b * n⁻¹ := by
    rcases h.mem_or (hconjP b h.b_mem) with ⟨v, hv⟩ | hv
    · exfalso
      apply h.bA
      have : b = a ^ v := by
        calc b = n⁻¹ * (n * b * n⁻¹) * n := by group
          _ = a ^ v := by rw [← hv, hconjinv]
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · exact hv
  have hconjpow : ∀ i : ℤ, n * a ^ i * n⁻¹ = a ^ i := by
    intro i
    rw [← _root_.conj_zpow, hu1]
  have hσb : ∀ k : ℕ, n ^ k * b * (n ^ k)⁻¹ = a ^ ((k : ℤ) * v) * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc n ^ (k + 1) * b * (n ^ (k + 1))⁻¹ = n * (n ^ k * b * (n ^ k)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = (n * a ^ ((k : ℤ) * v) * n⁻¹) * (n * b * n⁻¹) := by rw [ih]; group
        _ = a ^ (((k + 1 : ℕ) : ℤ) * v) * b := by
            rw [hconjpow, ← hv, ← mul_assoc, ← zpow_add]
            congr 2
            push_cast
            ring
  have hb1 : n * b * n⁻¹ = b := by
    have h1 := hσb m
    rw [hnm, one_mul, inv_one, mul_one] at h1
    have h2 : a ^ ((m : ℤ) * v) = 1 := by
      have := congrArg (· * b⁻¹) h1
      simpa using this.symm
    rw [h.zpow_eq_one_iff] at h2
    have hcop : IsCoprime (8 * M : ℤ) (m : ℤ) := by
      rw [h8]
      exact isCoprime_two_pow_of_odd (by exact_mod_cast hn) _
    have h3 := hcop.dvd_of_dvd_mul_left h2
    rw [← hv, (h.zpow_eq_one_iff _).mpr h3, one_mul]
  have hle : P ≤ Subgroup.centralizer ({n} : Set G) := by
    rw [← h.eq]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * n = n * (n⁻¹ * a * n) := by group
        _ = n * a := by rw [hinv]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc b * n = n * b * n⁻¹ * n := by rw [hb1]
        _ = n * b := by group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)


end SDData

@[expose] def GoldschmidtB3Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), A ≤ (S : Subgroup G) →
    fusionStronglyClosed (A : Set G) S →
    (∀ n ∈ Subgroup.normalizer (A : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (A : Set G)) →
    IsSylow2In A (Subgroup.normalClosure (A : Set G))

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem exists_conj_mem_sylow_ne [IsSimpleGroup G] (ht : S19R.TightStd p f K z) (S : Sylow 2 G)
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hI.sq) hI.ne_one
  have hiso : ∀ g : G, g * z * g⁻¹ * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have hu : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hg
    have hu2 : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]
    obtain ⟨c, hc, hcS⟩ := exists_conj_mem_of_sylow_le S hSz hu hu2
    have h1 := hcon (c * g) (by
      rw [show c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ by group]; exact hcS)
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc g * z * g⁻¹ = c⁻¹ * (c * g * z * (c * g)⁻¹) * c := by group
      _ = c⁻¹ * (z * c) := by rw [h1, mul_assoc]
      _ = z := by rw [← hcz]; group
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G z hI.ne_one hI.sq hiso
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · obtain ⟨x, y, hxy⟩ := ht.branch.nonabelian
    have hzZ : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hN g
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hzZ
      exact hI.ne_one hzZ
    · have := Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top x) y
      exact hxy this.symm
  · rw [htop, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    obtain ⟨c, hc⟩ := hNodd
    omega


end CFSG.ClassicalInvolution.Disconnected.AschTight
