module

public import CFSG.Timmesfeld.Opposite.Basic

public section

namespace CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

theorem eq_of_sq_eq_of_odd {x y : G} (hx : Odd (orderOf x)) (hy : Odd (orderOf y))
    (h : x ^ 2 = y ^ 2) : x = y := by
  have hox : orderOf (x ^ 2) = orderOf x := by
    rw [orderOf_pow' _ two_ne_zero, Nat.Coprime.gcd_eq_one
      (Nat.coprime_comm.1 ((Nat.coprime_two_left).2 hx)), Nat.div_one]
  have hoy : orderOf (y ^ 2) = orderOf y := by
    rw [orderOf_pow' _ two_ne_zero, Nat.Coprime.gcd_eq_one
      (Nat.coprime_comm.1 ((Nat.coprime_two_left).2 hy)), Nat.div_one]
  have hm : orderOf x = orderOf y := by rw [← hox, ← hoy, h]
  obtain ⟨k, hk⟩ := hx
  have key : ∀ w : G, orderOf w = 2 * k + 1 → w = (w ^ 2) ^ (k + 1) := by
    intro w hw
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hw,
      pow_orderOf_eq_one, one_mul]
  rw [key x hk, key y (hm ▸ hk), h]

theorem eq_of_commute_mul_of_odd {a b e : G} (ha : a * a = 1) (hb : b * b = 1) (he : e * e = 1)
    (hea : Odd (orderOf (e * a))) (heb : Odd (orderOf (e * b)))
    (hcomm : Commute e (a * b)) : a = b := by
  have h1 : (e * a * e) * (e * b * e) = a * b := by
    have : e * (a * b) * e = a * b := by
      rw [hcomm.eq, mul_assoc, he, mul_one]
    calc (e * a * e) * (e * b * e) = e * a * (e * e) * b * e := by group
      _ = e * (a * b) * e := by rw [he]; group
      _ = a * b := this
  have h2 : (e * b * e) * b = (e * a * e) * a := by
    have hae : (e * a * e) * (e * a * e) = 1 := by
      calc (e * a * e) * (e * a * e) = e * a * (e * e) * a * e := by group
        _ = e * (a * a) * e := by rw [he]; group
        _ = 1 := by rw [ha, mul_one, he]
    have : e * b * e = (e * a * e) * (a * b) := by
      calc e * b * e = ((e * a * e) * (e * a * e)) * (e * b * e) := by rw [hae, one_mul]
        _ = (e * a * e) * ((e * a * e) * (e * b * e)) := by group
        _ = (e * a * e) * (a * b) := by rw [h1]
    rw [this]
    calc e * a * e * (a * b) * b = e * a * e * a * (b * b) := by group
      _ = e * a * e * a := by rw [hb, mul_one]
  have hsq : (e * a) ^ 2 = (e * b) ^ 2 := by
    have ea : (e * a) ^ 2 = (e * a * e) * a := by rw [pow_two]; group
    have eb : (e * b) ^ 2 = (e * b * e) * b := by rw [pow_two]; group
    rw [ea, eb, h2]
  exact mul_left_cancel (eq_of_sq_eq_of_odd hea heb hsq)

theorem third_kind {c u : G} (hc : c * c = 1) (hu : u * u = 1) {m : ℕ} (hmodd : Odd m)
    (hm : orderOf (c * u) = 2 * m) :
    Commute ((c * u) ^ m) c ∧ Commute ((c * u) ^ m) u ∧
      ∃ h ∈ Subgroup.closure ({c, u} : Set G), h * c * h⁻¹ = u * (c * u) ^ m := by
  set g := c * u with hg
  have hpow : g ^ (2 * m) = 1 := hm ▸ pow_orderOf_eq_one g
  have hinvm : (g ^ m)⁻¹ = g ^ m := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, hpow]
  have hcz : c * g ^ m = g ^ m * c := by
    have h := mul_zpow_mul_eq_zpow_neg_mul hc hu (m : ℤ)
    rw [zpow_neg, zpow_natCast, hinvm] at h
    exact h
  have hu' : u = c * g := by rw [hg, ← mul_assoc, hc, one_mul]
  refine ⟨hcz.symm, ?_, ?_⟩
  · change g ^ m * u = u * g ^ m
    rw [hu', ← mul_assoc, ← hcz, mul_assoc, mul_assoc, ← pow_succ, ← pow_succ']
  · obtain ⟨k, hk⟩ := hmodd
    refine ⟨g ^ (-((k + 1 : ℕ) : ℤ)), Subgroup.zpow_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) _, ?_⟩
    have hconj := mul_zpow_mul_eq_zpow_neg_mul hc hu ((k + 1 : ℕ) : ℤ)
    rw [← hg] at hconj
    calc g ^ (-((k + 1 : ℕ) : ℤ)) * c * (g ^ (-((k + 1 : ℕ) : ℤ)))⁻¹
        = g ^ (-((k + 1 : ℕ) : ℤ)) * (c * g ^ ((k + 1 : ℕ) : ℤ)) := by
          rw [zpow_neg, inv_inv, mul_assoc]
      _ = g ^ (-((k + 1 : ℕ) : ℤ)) * (g ^ (-((k + 1 : ℕ) : ℤ)) * c) := by rw [hconj]
      _ = c * g ^ (((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ)) := by
          rw [← mul_assoc, ← zpow_add, ← neg_add]
          have h2 := mul_zpow_mul_eq_zpow_neg_mul hc hu
            (((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ))
          rw [← hg] at h2
          rw [h2]
      _ = c * g ^ (m + 1) := by
          rw [← zpow_natCast]
          congr 2
          push_cast
          omega
      _ = u * g ^ m := by rw [pow_succ', ← mul_assoc, ← hu']

@[expose] def RankOneOpposite (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∀ x ∈ Subgroup.closure (rootSet D d ∪ rootSet D c),
      x * d * x⁻¹ ∈ rootSet D d ∨
        (¬ Commute d (x * d * x⁻¹) ∧ Odd (orderOf (d * (x * d * x⁻¹))))

@[expose] def NoCommonCentral (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∀ w ∈ rootGroup D d, Commute w c → w = 1

theorem trichotomy [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hA : RankOneOpposite D) {d a b c : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) :
    a * b ∈ rootSet D d ∨ a * b * c * (a * b)⁻¹ ∈ rootSet D c ∨
      ∃ z ∈ rootGroup D d, z ≠ 1 ∧ Commute z c := by
  have hd2 := hD.mul_self_eq_one hd
  have hc2 := hD.mul_self_eq_one hc
  have ha2 := hD.mul_self_eq_one ha.1
  have hb2 := hD.mul_self_eq_one hb.1
  set u := a * b with hu
  have huW : u ∈ rootGroup D d := (rootGroup D d).mul_mem (rootSet_subset_rootGroup D d ha)
    (rootSet_subset_rootGroup D d hb)
  have hu2 : u * u = 1 := mul_self_eq_one_of_mem_rootGroup hD hd huW
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  by_cases h1 : Odd (orderOf (c * u))
  · exact Or.inl (mem_rootSet_of_mem_rootGroup hclass hd
      (mem_of_odd_orderOf_mul hclass hD hc hu2 h1) huW)
  by_cases h2 : u * c * u⁻¹ ∈ rootSet D c
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  set X := Subgroup.closure (rootSet D d ∪ rootSet D c) with hX
  have hdX : d ∈ X := Subgroup.subset_closure (Or.inl (mem_rootSet_self hd))
  have hcX : c ∈ X := Subgroup.subset_closure (Or.inr (mem_rootSet_self hc))
  have huX : u ∈ X := X.mul_mem (Subgroup.subset_closure (Or.inl ha))
    (Subgroup.subset_closure (Or.inl hb))
  set σ := dihedralSwap d c with hσ
  have hσX : σ ∈ X := X.mul_mem hdX (X.pow_mem (X.mul_mem hdX hcX) _)
  have hσ2 : σ * σ = 1 := dihedralSwap_mul_self hd2 hc2
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσd : σ * d * σ⁻¹ = c := dihedralSwap_conj hd2 hc2 hodd
  have hσc : σ * c * σ⁻¹ = d := dihedralSwap_conj' hd2 hc2 hodd
  set c' := u * c * u⁻¹ with hc'
  have hx1 : (σ * u * σ⁻¹) * d * (σ * u * σ⁻¹)⁻¹ = σ * c' * σ⁻¹ := by
    have : σ⁻¹ * d * σ = c := by rw [hσinv]; simpa [hσinv] using hσd
    calc (σ * u * σ⁻¹) * d * (σ * u * σ⁻¹)⁻¹ = σ * u * (σ⁻¹ * d * σ) * u⁻¹ * σ⁻¹ := by group
      _ = σ * c' * σ⁻¹ := by rw [this, hc']; group
  have hA1 := hA d hd c hc hdc hodd (σ * u * σ⁻¹) (X.mul_mem (X.mul_mem hσX huX) (X.inv_mem hσX))
  rw [hx1] at hA1
  rcases hA1 with hin | ⟨hnc, hoddc⟩
  · exfalso
    apply h2
    have hmem : σ⁻¹ * (σ * c' * σ⁻¹) * σ⁻¹⁻¹ ∈ rootSet D (σ⁻¹ * d * σ⁻¹⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨_, hin, rfl⟩
    have e1 : σ⁻¹ * (σ * c' * σ⁻¹) * σ⁻¹⁻¹ = c' := by group
    have e2 : σ⁻¹ * d * σ⁻¹⁻¹ = c := by rw [inv_inv, hσinv]; simpa [hσinv] using hσd
    rwa [e1, e2] at hmem
  have hcc' : ¬ Commute c c' := by
    intro h
    apply hnc
    rw [← hσc]
    exact (Commute.conj_iff σ).2 h
  have hocc : Odd (orderOf (c * c')) := by
    rw [← orderOf_conj_eq σ, show σ * (c * c') * σ⁻¹ = (σ * c * σ⁻¹) * (σ * c' * σ⁻¹) by group,
      hσc]
    exact hoddc
  have hsq : c * c' = (c * u) ^ 2 := by rw [hc', huinv, pow_two]; group
  rw [hsq] at hocc
  have hfin : orderOf (c * u) ≠ 0 := (orderOf_pos (c * u)).ne'
  have heven : Even (orderOf (c * u)) := Nat.not_odd_iff_even.1 h1
  obtain ⟨m, hm⟩ := heven
  have hm' : orderOf (c * u) = 2 * m := by omega
  have hosq : orderOf ((c * u) ^ 2) = m := by
    rw [orderOf_pow' _ two_ne_zero, hm', Nat.gcd_eq_right (dvd_mul_right 2 m)]
    omega
  have hmodd : Odd m := hosq ▸ hocc
  obtain ⟨hzc, hzu, h, hh, hhc⟩ := third_kind hc2 hu2 hmodd hm'
  set z := (c * u) ^ m with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hdvd := orderOf_dvd_of_pow_eq_one hz1
    rw [hm'] at hdvd
    have hm0 : 0 < m := hmodd.pos
    have := Nat.le_of_dvd hm0 hdvd
    omega
  set e := u * z with he
  have heD : e ∈ D := by rw [← hhc]; exact conj_mem_of_isClass hclass h hc
  have hhX : h ∈ X := by
    refine (Subgroup.closure_le X).2 ?_ hh
    rintro y (rfl | rfl)
    · exact hcX
    · exact huX
  have hx2 : (h * σ) * d * (h * σ)⁻¹ = e := by
    rw [← hhc, ← hσd]
    group
  have hA2 := hA d hd c hc hdc hodd (h * σ) (X.mul_mem hhX hσX)
  rw [hx2] at hA2
  have heu : Commute e u := by
    show u * z * u = u * (u * z)
    rw [mul_assoc, ← hzu.eq]
  rcases hA2 with heT | ⟨hne, hoe⟩
  · refine ⟨z, ?_, hz1, hzc⟩
    have : z = u * e := by rw [he, ← mul_assoc, hu2, one_mul]
    rw [this]
    exact (rootGroup D d).mul_mem huW (rootSet_subset_rootGroup D d heT)
  · exfalso
    have hae : Odd (orderOf (a * e)) := (odd_orderOf_mul_iff_of_mem_rootSet hD hd ha heD hne).2 hoe
    have hbe : Odd (orderOf (b * e)) := (odd_orderOf_mul_iff_of_mem_rootSet hD hd hb heD hne).2 hoe
    rw [← orderOf_mul_comm_eq] at hae hbe
    exact hab (eq_of_commute_mul_of_odd ha2 hb2 (hD.mul_self_eq_one heD) hae hbe heu)


theorem noCommonCentral_of_gen (h : Hyp G D)
    (hgen : ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
      Subgroup.closure (insert c {f | f ∈ D ∧ Commute d f}) = ⊤) :
    NoCommonCentral D := by
  intro d hd c hc hdc hodd w hw hwc
  have hcent : w ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure (insert c {f | f ∈ D ∧ Commute d f}) := by
      rw [hgen d hd c hc hdc hodd]; exact Subgroup.mem_top g
    have key : Commute g w := by
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | ⟨hxD, hdx⟩
        · exact hwc.symm
        · exact (commute_of_mem_rootGroup_of_commute hw hxD hdx).symm
      | one => exact Commute.one_left w
      | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
      | inv x _ ih => exact ih.inv_left
    exact key.eq
  rw [h.center_eq_bot, Subgroup.mem_bot] at hcent
  exact hcent

@[expose] def CommConnected (D : Set G) : Prop :=
  ∀ S ⊆ D, S.Nonempty → (∀ x ∈ S, ∀ y ∈ D, Commute x y → y ∈ S) → D ⊆ S


end CFSG.Timmesfeld.Closure
