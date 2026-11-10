module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem mem_normalizer_of_mul_self_eq_one {H : Subgroup G} {b : G} (hb : b * b = 1)
    (h : ∀ x ∈ H, b * x * b⁻¹ ∈ H) : b ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 := h _ hx
  have e : b * (b * x * b⁻¹) * b⁻¹ = (b * b) * x * (b * b)⁻¹ := by group
  rwa [e, hb, one_mul, inv_one, mul_one] at h1

theorem mem_or_mul_mem_of_mem_sup_zpowers {R : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R ⊔ Subgroup.zpowers t) :
    x ∈ R ∨ x * t ∈ R := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr htN
  have hx' : x ∈ ((R ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hle] at hx'
  obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rwa [← two_mul, zpow_mul, h2, one_zpow, mul_one]
  · right
    rwa [zpow_add_one, zpow_mul, h2, one_zpow, one_mul, mul_assoc, ht, mul_one]

theorem mul_self_mem_of_mem_sup_zpowers {R : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R ⊔ Subgroup.zpowers t) :
    x * x ∈ R := by
  rcases mem_or_mul_mem_of_mem_sup_zpowers ht htN hx with h | h
  · exact R.mul_mem h h
  · have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hconj : t * (x * t) * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp htN _).mp h
    have e : x * t * (t * (x * t) * t⁻¹) = x * x := by
      rw [ht']
      simp only [mul_assoc]
      rw [ht, mul_one, ← mul_assoc t t x, ht, one_mul]
    rw [← e]
    exact R.mul_mem h hconj

theorem closure_pair_eq_sup_zpowers (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem zpow_eq_zpow_of_mul_self_eq_one {g : G} {i j : ℤ} (hi : g ^ i * g ^ i = 1)
    (hj : g ^ j * g ^ j = 1) (hi1 : g ^ i ≠ 1) (hj1 : g ^ j ≠ 1) : g ^ i = g ^ j := by
  have hi' : g ^ (i + i) = 1 := by rw [zpow_add]; exact hi
  have hj' : g ^ (j + j) = 1 := by rw [zpow_add]; exact hj
  obtain ⟨e, he⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hi'
  obtain ⟨f, hf⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hj'
  have hodd : ∀ {k c : ℤ}, g ^ k ≠ 1 → k + k = (orderOf g : ℤ) * c → Odd c := by
    intro k c hk hc
    rcases Int.even_or_odd c with ⟨c', rfl⟩ | h
    · exact absurd (orderOf_dvd_iff_zpow_eq_one.mp ⟨c', by linarith⟩) hk
    · exact h
  obtain ⟨d, hd⟩ := (hodd hi1 he).sub_odd (hodd hj1 hf)
  have h2 : 2 * (i - j) = 2 * ((orderOf g : ℤ) * d) := by
    linear_combination he - hf + (orderOf g : ℤ) * hd
  have hij : g ^ (i - j) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp ⟨d, mul_left_cancel₀ two_ne_zero h2⟩
  rw [zpow_sub, mul_inv_eq_one] at hij
  exact hij

theorem exists_conj_eq_mul_of_isSemidihedral [Finite G] {R : Subgroup G} {z t : G}
    (hR2 : IsPGroup 2 R) (hz : IsUniqueInvolution R z) (ht : t * t = 1) (htR : t ∉ R)
    (htN : t ∈ Subgroup.normalizer (R : Set G))
    (hsd : IsSemidihedral (R ⊔ Subgroup.zpowers t)) : ∃ r ∈ R, r * t * r⁻¹ = z * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, ha8, -, hb2, -, hbab, hcl⟩ := hsd
  have haP : a ∈ R ⊔ Subgroup.zpowers t := hcl ▸ Subgroup.subset_closure (by simp)
  have htP : t ∈ R ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := fun h => htR (h ▸ R.one_mem)
  have hzt2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact ht) ht1
  have hP2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers t) :=
    hR2.to_sup_of_normal_left' hzt2 (Subgroup.zpowers_le.mpr htN)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hadvd : orderOf a ∣ 2 ^ n := hn ▸ Subgroup.orderOf_dvd_natCard _ haP
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hadvd
  have he3 : 3 ≤ e := by
    by_contra h
    have : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, orderOf a = 8 * M :=
    ⟨2 ^ (e - 3), by rw [he, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.add_sub_cancel' he3]⟩
  have hM1 : 1 ≤ M := by omega
  have ha2 : a * a ∈ R := mul_self_mem_of_mem_sup_zpowers ht htN haP
  have hpow : ∀ m : ℕ, a ^ (2 * m) ∈ R := fun m => by
    rw [pow_mul, sq]
    exact R.pow_mem ha2 m
  have htA : t ∉ Subgroup.zpowers a := by
    intro hta
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hta
    have hk2 : a ^ (k + k) = 1 := by rw [zpow_add]; exact ht
    obtain ⟨d, hd⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hk2
    rw [hM] at hd
    push_cast at hd
    have hk : k = 2 * (2 * M * d) := by linarith
    apply htR
    rw [hk, zpow_mul, zpow_two]
    exact R.zpow_mem ha2 _
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    refine mem_normalizer_of_mul_self_eq_one hb2 fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hbab]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _) _
  have htab : t ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [← closure_pair_eq_sup_zpowers, hcl]
    exact htP
  obtain ⟨i, hi⟩ : ∃ i : ℤ, a ^ i = t * b := by
    rcases mem_or_mul_mem_of_mem_sup_zpowers hb2 hbN htab with h | h
    · exact absurd h htA
    · exact Subgroup.mem_zpowers_iff.mp h
  have hti : t = a ^ i * b := by rw [hi, mul_assoc, hb2, mul_one]
  obtain ⟨s, hs⟩ : ∃ s : G, a ^ (2 * M) = s := ⟨_, rfl⟩
  have hk : orderOf a / 2 - 1 = 4 * M - 1 := by omega
  have hbs : b * s * b⁻¹ = s⁻¹ := by
    rw [← hs, ← conj_pow, hbab, hk, ← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    have h1 : (4 * M - 1) * (2 * M) + 2 * M = orderOf a * M := by
      rw [hM, ← add_one_mul, Nat.sub_add_cancel (by omega)]
      ring
    rw [h1, pow_mul, pow_orderOf_eq_one, one_pow]
  have hbs' : b * s⁻¹ = s * b := by
    have h1 : (b * s * b⁻¹)⁻¹ = s := by rw [hbs, inv_inv]
    calc b * s⁻¹ = (b * s * b⁻¹)⁻¹ * b := by group
      _ = s * b := by rw [h1]
  have hcomm : a ^ i * s = s * a ^ i := by
    rw [← hs, ← zpow_natCast, zpow_mul_comm]
  have hssR : s * s ∈ R := by rw [← hs]; exact R.mul_mem (hpow M) (hpow M)
  have hss1 : s * s ≠ 1 := by
    rw [← hs, ← pow_add]
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hM]; omega)
  have hss2 : s * s * (s * s) = 1 := by
    rw [← hs, ← pow_add, ← pow_add, show 2 * M + 2 * M + (2 * M + 2 * M) = orderOf a by
      rw [hM]; ring, pow_orderOf_eq_one]
  have hzs : s * s = z := (hz.unique _ hssR hss2).resolve_left hss1
  refine ⟨s, by rw [← hs]; exact hpow M, ?_⟩
  calc s * t * s⁻¹ = s * a ^ i * (b * s⁻¹) := by rw [hti]; group
    _ = s * (a ^ i * s) * b := by rw [hbs']; group
    _ = s * (s * a ^ i) * b := by rw [hcomm]
    _ = s * s * (a ^ i * b) := by group
    _ = z * t := by rw [hzs, ← hti]

theorem exists_zpow_mul_zpow_of_mem_sup {a c : G} (hac : a * c = c * a) {x : G}
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c) : ∃ i j : ℤ, a ^ i * c ^ j = x := by
  have hle : Subgroup.zpowers a ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute c a from hac.symm) k).eq
  have hx' : x ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨i, j, rfl⟩

theorem mul_comm_of_mem_sup_zpowers {a c : G} (hac : a * c = c * a) {x y : G}
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    (hy : y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c) : x * y = y * x := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac hx
  obtain ⟨k, l, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac hy
  have h : Commute a c := hac
  have h1 : Commute (a ^ i * c ^ j) (a ^ k) :=
    (Commute.zpow_zpow_self a i k).mul_left (h.symm.zpow_zpow j k)
  have h2 : Commute (a ^ i * c ^ j) (c ^ l) :=
    (h.zpow_zpow i l).mul_left (Commute.zpow_zpow_self c j l)
  exact (h1.mul_right h2).eq


end CFSG.ClassicalInvolution.Disconnected.AschTight
