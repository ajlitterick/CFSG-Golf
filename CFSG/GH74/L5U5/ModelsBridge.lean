module

public import CFSG.GH74.L5U5.ModelsInvolution

public section

namespace CFSG.GH74.L5U5

open CFSG.GH74 CFSG.GH74.Filter CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

section Counting

variable {C : Type*} [Group C]

theorem q8Frattini_a_two : q8Frattini (QuaternionGroup.a 2) = 1 := by decide

theorem q8Frattini_eq_one_of_central (g : Q8) (hg : ∀ x, g * x = x * g) : q8Frattini g = 1 := by
  rcases quaternion_center g hg with rfl | rfl
  · exact map_one _
  · exact q8Frattini_a_two

theorem V4_sq : ∀ a : V4, a ^ 2 = 1 := by decide

theorem central_of_comm_q8q8 {φ : Q8 × Q8 →* C} (hφ : Function.Injective φ) {g : Q8 × Q8}
    (hg : ∀ a : Q8 × Q8, φ a * φ g = φ g * φ a) : ∀ a : Q8 × Q8, g * a = a * g := by
  intro a
  apply hφ
  rw [map_mul, map_mul]
  exact (hg a).symm

theorem q8q8_commuting_two_subgroup_le [Finite C] (hC : Gen4 C) (φ : Q8 × Q8 →* C)
    (hφ : Function.Injective φ) (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Q8 × Q8) (t : C), t ∈ T → φ a * t = t * φ a) : T ≤ φ.range := by
  by_contra hnot
  set M : Subgroup T := φ.range.subgroupOf T with hM
  have hMc : ∀ t ∈ M, ∀ s : T, s * t = t * s := by
    intro t ht s
    obtain ⟨a, ha⟩ := (Subgroup.mem_subgroupOf.1 ht)
    apply Subtype.ext
    change (s : C) * (t : C) = (t : C) * (s : C)
    rw [← ha]
    exact (hcomm a s s.2).symm
  have hMn : M.Normal :=
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hMc n hn g
      rw [this]
      exact hn⟩
  have hMtop : M ≠ ⊤ := by
    intro htop
    apply hnot
    intro t ht
    have : (⟨t, ht⟩ : T) ∈ M := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hQ : IsPGroup 2 (T ⧸ M) := hT.to_quotient M
  have hnil : Group.IsNilpotent (T ⧸ M) := hQ.isNilpotent
  have hdvd : 2 ∣ Nat.card (T ⧸ M) := by
    rcases hQ.card_eq_or_dvd with h | h
    · exfalso
      apply hMtop
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
      exact h
    · exact h
  obtain ⟨H, hHidx, hHn⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := T ⧸ M) (k := 2) hdvd
  have _ := hHn
  have hEcard : Nat.card ((T ⧸ M) ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hHidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcyc : IsCyclic ((T ⧸ M) ⧸ H) := isCyclic_of_prime_card hEcard
  let _ : CommGroup ((T ⧸ M) ⧸ H) := IsCyclic.commGroup
  have hEsq : ∀ e : (T ⧸ M) ⧸ H, e ^ 2 = 1 := fun e => by
    rw [← hEcard]; exact pow_card_eq_one'
  let τ : T →* (T ⧸ M) ⧸ H := (QuotientGroup.mk' H).comp (QuotientGroup.mk' M)
  have hτ : Function.Surjective τ :=
    (QuotientGroup.mk'_surjective H).comp (QuotientGroup.mk'_surjective M)
  let α : (Q8 × Q8) × T →* C :=
    MonoidHom.noncommCoprod φ T.subtype (fun a t => (hcomm a t t.2 : _))
  let β : (Q8 × Q8) × T →* (V4 × V4) × ((T ⧸ M) ⧸ H) :=
    (q8Frattini.prodMap q8Frattini).prodMap τ
  have hβ : Function.Surjective β :=
    (q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap hτ
  refine not_gen4_of_surjection α β hβ ?_ ?_ ?_ ?_ hC
  · intro a b
    exact Prod.ext (Prod.ext (mul_comm _ _) (mul_comm _ _)) (mul_comm _ _)
  · intro a
    exact Prod.ext (Prod.ext (V4_sq _) (V4_sq _)) (hEsq _)
  · rw [Nat.card_prod, Nat.card_prod, card_V4, hEcard]
    norm_num
  · rintro ⟨g, t⟩ hgt
    rw [MonoidHom.mem_ker] at hgt ⊢
    have h1 : φ g * (t : C) = 1 := hgt
    have htg : (t : C) = (φ g)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have htM : t ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf, htg]
      exact φ.range.inv_mem ⟨g, rfl⟩
    have hcent : ∀ a : Q8 × Q8, φ a * φ g = φ g * φ a := by
      intro a
      have hgT : φ g ∈ T := by
        have : (φ g) = ((t : C))⁻¹ := by rw [htg, inv_inv]
        rw [this]
        exact T.inv_mem t.2
      exact hcomm a (φ g) hgT
    have hgc := central_of_comm_q8q8 hφ hcent
    have hg1 : ∀ x : Q8, g.1 * x = x * g.1 := fun x => by
      have := congrArg Prod.fst (hgc (x, 1))
      simpa using this
    have hg2 : ∀ x : Q8, g.2 * x = x * g.2 := fun x => by
      have := congrArg Prod.snd (hgc (1, x))
      simpa using this
    change ((q8Frattini g.1, q8Frattini g.2), τ t) = 1
    refine Prod.ext (Prod.ext (q8Frattini_eq_one_of_central _ hg1)
      (q8Frattini_eq_one_of_central _ hg2)) ?_
    change τ t = 1
    have : (QuotientGroup.mk' M) t = 1 := (QuotientGroup.eq_one_iff t).2 htM
    change (QuotientGroup.mk' H) ((QuotientGroup.mk' M) t) = 1
    rw [this, map_one]

end Counting

section Consequences

variable {C : Type*} [Group C] [Finite C]

theorem q8q8_commuting_two_subgroup_le_center (hC : Gen4 C) (φ : Q8 × Q8 →* C)
    (hφ : Function.Injective φ) (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Q8 × Q8) (t : C), t ∈ T → φ a * t = t * φ a) :
    ∀ t ∈ T, ∃ g : Q8 × Q8, φ g = t ∧ ∀ a : Q8 × Q8, g * a = a * g := by
  intro t ht
  obtain ⟨g, hg⟩ := q8q8_commuting_two_subgroup_le hC φ hφ T hT hcomm ht
  refine ⟨g, hg, central_of_comm_q8q8 hφ fun a => ?_⟩
  rw [hg]
  exact hcomm a t ht

omit [Finite C] in
theorem isPGroup_zpowers_of_orderOf_eq_two {g : C} (h : orderOf g = 2) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have hg : g ^ 2 = 1 := h ▸ pow_orderOf_eq_one g
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change (g ^ n) ^ (2 ^ 1) = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

omit [Finite C] in
theorem isPGroup_two_sup_zpowers (A : Subgroup C) (hA : IsPGroup 2 A) (w : C) (hw : w * w = 1)
    (hnorm : ∀ a ∈ A, w * a * w⁻¹ ∈ A) : IsPGroup 2 ↥(A ⊔ Subgroup.zpowers w) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hnorm' : ∀ a ∈ A, w * a * w ∈ A := fun a ha => by
    have := hnorm a ha
    rwa [hwinv] at this
  have key : ∀ g ∈ A ⊔ Subgroup.zpowers w, g ∈ A ∨ g * w ∈ A := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact Or.inl hg
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have hw2 : w ^ 2 = 1 := by rw [sq]; exact hw
        obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
        · left
          rw [zpow_mul, zpow_ofNat, hw2, one_zpow]
          exact A.one_mem
        · right
          rw [zpow_add_one, zpow_mul, zpow_ofNat, hw2, one_zpow, one_mul, hw]
          exact A.one_mem
    | one => exact Or.inl A.one_mem
    | mul g₁ g₂ _ _ h₁ h₂ =>
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact Or.inl (A.mul_mem h₁ h₂)
      · exact Or.inr (by rw [mul_assoc]; exact A.mul_mem h₁ h₂)
      · refine Or.inr ?_
        have : g₁ * g₂ * w = (g₁ * w) * (w * g₂ * w) := by
          calc g₁ * g₂ * w = g₁ * (w * w) * g₂ * w := by rw [hw, mul_one]
            _ = (g₁ * w) * (w * g₂ * w) := by group
        rw [this]
        exact A.mul_mem h₁ (hnorm' _ h₂)
      · refine Or.inl ?_
        have : g₁ * g₂ = (g₁ * w) * (w * (g₂ * w) * w) := by
          calc g₁ * g₂ = g₁ * (w * w) * g₂ * (w * w) := by rw [hw]; group
            _ = (g₁ * w) * (w * (g₂ * w) * w) := by group
        rw [this]
        exact A.mul_mem h₁ (hnorm' _ h₂)
    | inv g _ h =>
      rcases h with h | h
      · exact Or.inl (A.inv_mem h)
      · refine Or.inr ?_
        have : g⁻¹ * w = w * (w * g⁻¹) * w := by
          calc g⁻¹ * w = (w * w) * g⁻¹ * w := by rw [hw, one_mul]
            _ = w * (w * g⁻¹) * w := by group
        have h' : w * g⁻¹ ∈ A := by
          have := A.inv_mem h
          rwa [mul_inv_rev, hwinv] at this
        rw [this]
        exact hnorm' _ h'
  rintro ⟨g, hg⟩
  rcases key g hg with hgA | hgw
  · obtain ⟨k, hk⟩ := hA ⟨g, hgA⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  · have hg2 : g ^ 2 ∈ A := by
      have : g ^ 2 = (g * w) * (w * (g * w) * w) := by
        calc g ^ 2 = g * g := sq g
          _ = g * (w * w) * g * (w * w) := by rw [hw]; group
          _ = (g * w) * (w * (g * w) * w) := by group
      rw [this]
      exact A.mul_mem hgw (hnorm' _ hgw)
    obtain ⟨k, hk⟩ := hA ⟨g ^ 2, hg2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 : (g ^ 2) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    change g ^ (2 ^ (k + 1)) = 1
    rw [pow_succ, mul_comm, pow_mul]
    exact h1

omit [Finite C] in
theorem card_Q8 : Nat.card Q8 = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

omit [Finite C] in
theorem isPGroup_range_q8q8 (φ : Q8 × Q8 →* C) : IsPGroup 2 φ.range := by
  rintro ⟨c, a, rfl⟩
  refine ⟨6, Subtype.ext ?_⟩
  change (φ a) ^ (2 ^ 6) = 1
  have h64 : a ^ 64 = 1 := by
    have := pow_card_eq_one' (G := Q8 × Q8) (x := a)
    rwa [Nat.card_prod, card_Q8] at this
  rw [← map_pow, show (2 : ℕ) ^ 6 = 64 by norm_num, h64, map_one]

omit [Finite C] in
theorem exists_conj_sylow {p : ℕ} [Fact p.Prime] [Finite C] (P Q : Sylow p C) :
    ∃ g : C, ∀ m : C, m ∈ (Q : Subgroup C) ↔ g⁻¹ * m * g ∈ (P : Subgroup C) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  refine ⟨g, fun m => ?_⟩
  rw [← hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
  · intro h
    refine ⟨g⁻¹ * m * g, h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

end Consequences

section Bridge

open CFSG

variable {G : Type} [Group G]

@[expose] def xbar (x : G) : CentralizerBar x :=
  QuotientGroup.mk
    (⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ : ↥(Subgroup.centralizer ({x} : Set G)))

theorem xbar_mem_center (x : G) : xbar x ∈ Subgroup.center (CentralizerBar x) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  change (QuotientGroup.mk g' : CentralizerBar x) * QuotientGroup.mk _ =
    QuotientGroup.mk _ * QuotientGroup.mk g'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 g'.2 x (Set.mem_singleton x)).symm

theorem xbar_mul_self {x : G} (hx : orderOf x = 2) : xbar x * xbar x = 1 := by
  change (QuotientGroup.mk _ : CentralizerBar x) * QuotientGroup.mk _ = 1
  rw [← QuotientGroup.mk_mul]
  have : (⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ : ↥(Subgroup.centralizer ({x} : Set G))) *
      ⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ = 1 :=
    Subtype.ext (by
      change x * x = 1
      rw [← sq, ← hx]
      exact pow_orderOf_eq_one x)
  rw [this]
  exact (QuotientGroup.mk_one _)

theorem xbar_ne_one [Finite G] {x : G} (hx : orderOf x = 2) : xbar x ≠ 1 := by
  intro h
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  have hord : orderOf (⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ : ↥(Subgroup.centralizer ({x} : Set G))) = 2 := by
    rw [← hx]
    exact Subgroup.orderOf_mk _ _
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥(Subgroup.centralizer ({x} : Set G)))
  rw [hord] at hdvd
  exact absurd (hcop.eq_one_of_dvd hdvd) (by norm_num)

theorem orderOf_xbar [Finite G] {x : G} (hx : orderOf x = 2) : orderOf (xbar x) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact xbar_mul_self hx) (xbar_ne_one hx)

theorem gen4_centralizerBar [Finite G] (hG : Gen4 G) (x : G) : Gen4 (CentralizerBar x) :=
  Gen4.quotient _ (Gen4.subgroup _ hG)

theorem commute_of_mem_zpowers_xbar (x : G) (c : CentralizerBar x) {t : CentralizerBar x}
    (ht : t ∈ Subgroup.zpowers (xbar x)) : c * t = t * c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h : Commute c (xbar x) := Subgroup.mem_center_iff.1 (xbar_mem_center x) c
  exact (h.zpow_right k).eq

variable [Finite G]


section SylowG

@[expose] def xH (x : G) : ↥(Subgroup.centralizer ({x} : Set G)) :=
  ⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]⟩


omit [Finite G] in
theorem xH_mul_self {x : G} (hx : orderOf x = 2) : xH x * xH x = 1 :=
  Subtype.ext (by
    change x * x = 1
    rw [← sq, ← hx]
    exact pow_orderOf_eq_one x)

omit [Finite G] in
theorem orderOf_xH {x : G} (hx : orderOf x = 2) : orderOf (xH x) = 2 := by
  refine orderOf_eq_prime (by rw [sq]; exact xH_mul_self hx) ?_
  intro h
  have : x = 1 := congrArg Subtype.val h
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

omit [Finite G] in
theorem xH_central (x : G) (g : ↥(Subgroup.centralizer ({x} : Set G))) : g * xH x = xH x * g :=
  Subtype.ext (Subgroup.mem_centralizer_iff.1 g.2 x (Set.mem_singleton x)).symm

omit [Finite G] in
theorem xH_mem_sylow {x : G} (hx : orderOf x = 2)
    (S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) : xH x ∈ (S : Subgroup _) := by
  have hN : (Subgroup.zpowers (xH x)).Normal :=
    ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have h : Commute g (xH x) := xH_central x g
      have : g * xH x ^ k * g⁻¹ = xH x ^ k := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (h.zpow_right k).eq
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _⟩
  exact (isPGroup_zpowers_of_orderOf_eq_two (orderOf_xH hx)).le_sylow_of_normal S
    (Subgroup.mem_zpowers _)

theorem eq_one_of_mem_sylow_of_mem_pPrimeCore {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    {n : H} (hS : n ∈ (S : Subgroup H)) (hN : n ∈ pPrimeCore 2 H) : n = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨n, hS⟩
  have hk' : n ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf n ∣ Nat.card (pPrimeCore 2 H) := Subgroup.orderOf_dvd_natCard _ hN
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
  have : Nat.Coprime (orderOf n) (2 ^ k) :=
    (Nat.Coprime.pow_right k (hcop.coprime_dvd_right h2).symm)
  have h3 := this.eq_one_of_dvd h1
  exact orderOf_eq_one_iff.1 h3


omit [Finite G] in
theorem isPGroup_subgroupOf {p : ℕ} {K : Subgroup G} (hK : IsPGroup p K) (H : Subgroup G) :
    IsPGroup p ↥(K.subgroupOf H) := by
  rintro ⟨h, hh⟩
  obtain ⟨k, hk⟩ := hK ⟨(h : G), Subgroup.mem_subgroupOf.1 hh⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

omit [Finite G] in
theorem zpow_eq_one_or_self {x : G} (hx : x * x = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hx
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_ofNat, hx2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_ofNat, hx2, one_zpow, one_mul]


end SylowG

end Bridge

end CFSG.GH74.L5U5
