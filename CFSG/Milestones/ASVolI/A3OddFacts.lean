module

public import CFSG.Milestones.ASVolI.A3
public import CFSG.Quasithin.Background.A3Structure315
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelMain
public import CFSG.Quasithin.Vol2.F134LieU3
public import CFSG.Quasithin.Background.A3Structure315Facts
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs

public section

namespace CFSG.ASVolI

open CFSG.Open


open scoped Pointwise in
theorem burnsideA315x_relIndex_sup {G : Type} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb


open scoped Pointwise in
theorem burnsideA315x_coe_sup {G : Type*} [Group G] {H K : Subgroup G}
    (h : (H : Set G) * K = K * H) : ((H ⊔ K : Subgroup G) : Set G) = H * K := by
  let T : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
        rw [← h] at hbc
        obtain ⟨c', hc', b', hb', hcb⟩ := hbc
        have hcb : c' * b' = b * c := hcb
        refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
        rw [← h] at hba
        show (a * b)⁻¹ ∈ (H : Set G) * K
        rw [_root_.mul_inv_rev]
        exact hba }
  have hT : H ⊔ K = T := le_antisymm
    (sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩))
    (fun x ⟨a, ha, b, hb, hab⟩ => hab ▸ Subgroup.mul_mem_sup ha hb)
  rw [hT]
  rfl

open scoped Pointwise in
theorem burnsideA315x_card_sup {G : Type*} [Group G] {H K : Subgroup G}
    (h : (H : Set G) * K = K * H) (hHK : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod]
  have hc := congrArg (fun s : Set G => Nat.card s) (burnsideA315x_coe_sup h)
  change Nat.card (H ⊔ K : Subgroup G) = Nat.card ((H : Set G) * K : Set G) at hc
  rw [hc]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun q : H × K =>
    (⟨(q.1 : G) * q.2, Set.mul_mem_mul q.1.2 q.2.2⟩ : ((H : Set G) * K : Set G))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have h' : a * b = a' * b' := congrArg Subtype.val hab
    have hm : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem ha') ha, hm ▸ K.mul_mem hb' (K.inv_mem hb)⟩
    rw [hHK, Subgroup.mem_bot] at hmem
    obtain rfl : a' = a := inv_mul_eq_one.mp hmem
    obtain rfl : b = b' := mul_left_cancel h'
    rfl
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩⟩
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

open scoped Pointwise in
theorem burnsideA315x_map_permute {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    ((H.map f : Subgroup G') : Set G') * (K.map f : Subgroup G') =
      (K.map f : Subgroup G') * (H.map f : Subgroup G') := by
  rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, h, Set.image_mul]


open scoped Pointwise in
structure burnsideA315x_Config (X : Type) [Group X] (S B : Subgroup X) : Prop where
  sylow : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤
  odd : Odd (Nat.card ↥B)
  not3 : ¬ IsPGroup 3 ↥B
  cases : IsMulCommutative ↥B ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥B
  perm : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)


theorem burnsideA315x_prime_dvd_lcm {r : ℕ} (hr : r.Prime) (M : Multiset ℕ) (h : r ∣ M.lcm) :
    ∃ c ∈ M, r ∣ c := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    exact absurd (Nat.le_of_dvd one_pos h) (by have := hr.two_le; omega)
  | cons a s ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm] at h
    rcases (Nat.Prime.dvd_lcm hr).1 h with h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨c, hc, hrc⟩ := ih h
      exact ⟨c, Multiset.mem_cons_of_mem hc, hrc⟩

theorem burnsideA315x_perm_two_primes {n r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (h1 : n < r + s) (h2 : n < r * s) (σ : Equiv.Perm (Fin n)) (hσr : r ∣ orderOf σ)
    (hσs : s ∣ orderOf σ) : False := by
  classical
  rw [← Equiv.Perm.lcm_cycleType] at hσr hσs
  obtain ⟨c, hc, hrc⟩ := burnsideA315x_prime_dvd_lcm hr _ hσr
  obtain ⟨c', hc', hsc'⟩ := burnsideA315x_prime_dvd_lcm hs _ hσs
  have hsum : σ.cycleType.sum ≤ n := by simpa using Equiv.Perm.sum_cycleType_le σ
  have hle : ∀ x ∈ σ.cycleType, x ≤ σ.cycleType.sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _)
  by_cases hcc : c = c'
  · subst hcc
    have hdvd : r * s ∣ c :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hr hs).2 hrs) hrc hsc'
    have hpos : 0 < c := by have := Equiv.Perm.two_le_of_mem_cycleType hc; omega
    have := Nat.le_of_dvd hpos hdvd
    have := hle c hc
    omega
  · have hc'e : c' ∈ σ.cycleType.erase c := (Multiset.mem_erase_of_ne (Ne.symm hcc)).2 hc'
    have e1 : σ.cycleType.sum = c + (σ.cycleType.erase c).sum := by
      conv_lhs => rw [← Multiset.cons_erase hc]
      rw [Multiset.sum_cons]
    have e2 : c' ≤ (σ.cycleType.erase c).sum :=
      Multiset.single_le_sum (fun _ _ => Nat.zero_le _) c' hc'e
    have hcr : r ≤ c := Nat.le_of_dvd (by have := Equiv.Perm.two_le_of_mem_cycleType hc; omega) hrc
    have hcs : s ≤ c' :=
      Nat.le_of_dvd (by have := Equiv.Perm.two_le_of_mem_cycleType hc'; omega) hsc'
    omega


theorem burnsideA315x_alt_odd_inner {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    {α : MulAut (alternatingGroup (Fin n))} (hα : Odd (orderOf α)) :
    ∃ l : alternatingGroup (Fin n), α = MulAut.conj l := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    hn α
  have hpow : ∀ k : ℕ, ∀ g : alternatingGroup (Fin n),
      (((α ^ k) g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = σ ^ k * g * (σ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ']
      group
  obtain ⟨j, hj⟩ := hα
  have hm : α ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one α
  have h6 : α ^ (2 * j + 2) = α := by rw [pow_succ, pow_succ, ← pow_succ, hm, one_mul]
  have hsign : Equiv.Perm.sign (σ ^ (2 * j + 2)) = 1 := by
    rw [map_pow, show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul, Int.units_sq, one_pow]
  refine ⟨⟨σ ^ (2 * j + 2), Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, MulEquiv.ext fun g => ?_⟩
  apply Subtype.ext
  calc ((α g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
      = (((α ^ (2 * j + 2)) g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by rw [h6]
    _ = σ ^ (2 * j + 2) * g * (σ ^ (2 * j + 2))⁻¹ := hpow _ g
    _ = _ := rfl


open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1.A6Model in
theorem burnsideA315x_alt6_odd_inner {α : MulAut (alternatingGroup (Fin 6))}
    (hα : Odd (orderOf α)) : ∃ l : alternatingGroup (Fin 6), α = MulAut.conj l := by
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  set φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm with hφ
  set b : ↥A6Models.autA6 := thetaEquiv φ α with hb
  have hbodd : Odd (orderOf b) := by
    rw [hb, MulEquiv.orderOf_eq]
    exact hα
  have hmem : (b : P10) ∈ A6Models.psl29 := by
    let N : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6
    haveI hN : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using psl29_normal (g : P10) g.2 (n : P10) hn⟩
    have hcardN : Nat.card N = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
    have hQ : Nat.card (↥A6Models.autA6 ⧸ N) = 4 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [card_autA6, hcardN] at this
      omega
    have h1 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ orderOf b :=
      orderOf_map_dvd (QuotientGroup.mk' N) b
    have h2 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ 4 := by
      rw [← hQ]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) = 1 := by
      have hodd := Odd.of_dvd_nat hbodd h1
      have hle := Nat.le_of_dvd (by norm_num) h2
      have hpos := orderOf_pos (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N)
      have hdiv : ∀ m, m ∣ 4 → m = 1 ∨ m = 2 ∨ m = 4 := by
        intro m hm
        have := Nat.le_of_dvd (by norm_num) hm
        interval_cases m <;> simp_all
      rcases hdiv _ h2 with h | h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
      · rw [h] at hodd; exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h3
    have := (QuotientGroup.eq_one_iff b).1 h3
    exact Subgroup.mem_subgroupOf.1 this
  refine ⟨ψ ⟨(b : P10), hmem⟩, MulEquiv.ext fun k => ?_⟩
  apply φ.injective
  apply Subtype.ext
  have hspec := thetaEquiv_spec φ α k
  rw [← hb] at hspec
  rw [hspec, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have : φ (ψ ⟨(b : P10), hmem⟩) = ⟨(b : P10), hmem⟩ := by simp [hφ]
  rw [this]
  rfl


theorem burnsideA315x_out_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ β : MulAut Y, Odd (orderOf β) → ∃ l : Y, β = MulAut.conj l) :
    ∀ α : MulAut X, Odd (orderOf α) → ∃ l : X, α = MulAut.conj l := by
  intro α hα
  have hodd : Odd (orderOf (MulAut.congr e α)) := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨l', hl'⟩ := h _ hodd
  refine ⟨e.symm l', MulEquiv.ext fun x => ?_⟩
  apply e.injective
  have h1 : (MulAut.congr e α) (e x) = (MulAut.conj l') (e x) := by rw [hl']
  have h2 : (MulAut.congr e α) (e x) = e (α x) := by
    show e (α (e.symm (e x))) = e (α x)
    rw [e.symm_apply_apply]
  have h3 : (MulAut.conj l') (e x) = e ((MulAut.conj (e.symm l')) x) := by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, e.apply_symm_apply]
  rw [h2, h3] at h1
  exact h1

theorem burnsideA315x_out_alt {X : Type} [Group X] {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (e : X ≃* alternatingGroup (Fin n)) :
    ∀ α : MulAut X, Odd (orderOf α) → ∃ l : X, α = MulAut.conj l := by
  refine burnsideA315x_out_of_mulEquiv e fun β hβ => ?_
  by_cases h6 : n = 6
  · subst h6
    exact burnsideA315x_alt6_odd_inner hβ
  · exact burnsideA315x_alt_odd_inner (by omega) hβ


open scoped Pointwise in
theorem burnsideA315x_Config.sup_card {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) :
    S ≤ B ⊔ S ∧ Nat.card ↥(B ⊔ S) = Nat.card ↥B * Nat.card ↥S := by
  obtain ⟨k, hk⟩ := hc.sylow.2.1.exists_card_eq
  have hdB : Nat.card ↥(B ⊓ S) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_left
  have hdS : Nat.card ↥(B ⊓ S) ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card ↥B) (2 ^ k) :=
    (Nat.coprime_two_left.2 hc.odd).symm.pow_right k
  have h1 : Nat.card ↥(B ⊓ S) ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdB hdS
  have hbot : B ⊓ S = ⊥ := Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
  exact ⟨le_sup_right, burnsideA315x_card_sup hc.perm hbot⟩

theorem burnsideA315x_Config.false_of_pow_three {X : Type} [Group X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) [Finite X] {k : ℕ} (h : Nat.card ↥B = 3 ^ k) : False :=
  hc.not3 (IsPGroup.of_card h)

theorem burnsideA315x_Config.exists_order_mul {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hrB : r ∣ Nat.card ↥B) (hsB : s ∣ Nat.card ↥B) : ∃ z : X, z ∈ B ∧ orderOf z = r * s := by
  rcases hc.cases with hab | ⟨q, hq, hBq⟩
  · haveI : Fact r.Prime := ⟨hr⟩
    haveI : Fact s.Prime := ⟨hs⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) s hsB
    have hcomm : Commute x y := hab.is_comm.comm x y
    have hcop : Nat.Coprime (orderOf x) (orderOf y) := by
      rw [hx, hy]
      exact (Nat.coprime_primes hr hs).2 hrs
    refine ⟨((x * y : ↥B) : X), (x * y : ↥B).2, ?_⟩
    rw [Subgroup.orderOf_coe, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy]
  · exfalso
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, hk⟩ := hBq.exists_card_eq
    rw [hk] at hrB hsB
    have h1 := (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hrB)
    have h2 := (Nat.prime_dvd_prime_iff_eq hs hq).1 (hs.dvd_of_dvd_pow hsB)
    exact hrs (h1.trans h2.symm)


theorem burnsideA315x_psl2_odd_inner {K : Type} [Field K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ k) (hk : k = 1 ∨ k = 2) :
    ∀ α : MulAut (CFSG.GorensteinWalter.PSL2 K), Odd (orderOf α) →
      ∃ x : CFSG.GorensteinWalter.PSL2 K, α = MulAut.conj x := by
  intro α hα
  set γ := (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).symm α
    with hγ
  have hγm : γ ^ orderOf α = 1 := by rw [hγ, ← map_pow, pow_orderOf_eq_one, map_one]
  have hψ : (SemidirectProduct.rightHom γ) ^ orderOf α = 1 := by rw [← map_pow, hγm, map_one]
  have hcard : Nat.card (RingAut K) = k :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have hcop : Nat.Coprime (orderOf α) k := by
    rcases hk with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact Nat.coprime_two_right.2 hα
  have hord : orderOf (SemidirectProduct.rightHom γ) = 1 := by
    have h1 : orderOf (SemidirectProduct.rightHom γ) ∣ orderOf α := orderOf_dvd_of_pow_eq_one hψ
    have h2 : orderOf (SemidirectProduct.rightHom γ) ∣ k := hcard ▸ orderOf_dvd_natCard _
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hψ1 : SemidirectProduct.rightHom γ = 1 := orderOf_eq_one_iff.mp hord
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hψ1
  have hg' : g ^ orderOf α = 1 := by
    apply CFSG.RankThree.PartTwo.KFacts.pglAction_injective
    rw [map_pow, hg, pow_orderOf_eq_one, map_one]
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd hα hg'
  refine ⟨x, ?_⟩
  rw [← hg, ← hx]
  exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL K x


theorem burnsideA315x_sylow_facts {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = p ^ e)
    {S : Subgroup (CFSG.GorensteinWalter.PSL2 F)} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card ↥S = 2 ^ (m + 1)) ∧ ¬ IsCyclic ↥S := by
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, e, hp, hp.odd_of_ne_two hp2, he, hF⟩
  have hD := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hS
  obtain ⟨m, hm, ⟨eS⟩⟩ := hD (h1.toSylow h2)
  have eS' : ↥S ≃* DihedralGroup (2 ^ m) := eS
  refine ⟨⟨m, hm, ?_⟩, fun hc => ?_⟩
  · rw [Nat.card_congr eS'.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  · have : IsCyclic (DihedralGroup (2 ^ m)) := isCyclic_of_surjective eS'.toMonoidHom eS'.surjective
    refine DihedralGroup.not_isCyclic (n := 2 ^ m) ?_ this
    intro h
    have : 2 ^ m = 2 ^ 0 := by rw [h]; rfl
    have := Nat.pow_right_injective (le_refl 2) this
    omega


theorem burnsideA315x_cyclic_of_le {X : Type} [Group X] {S H : Subgroup X} (hSH : S ≤ H)
    (hH : IsCyclic ↥H) : IsCyclic ↥S :=
  isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSH).surjective

theorem burnsideA315x_alt_no_order {Y : Type} [Group Y] {n : ℕ} (e : Y ≃* alternatingGroup (Fin n))
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (h1 : n < r + s) (h2 : n < r * s)
    (y : Y) (hy : orderOf y = r * s) : False := by
  have : orderOf ((e y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = r * s := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  refine burnsideA315x_perm_two_primes hr hs hrs h1 h2
    ((e y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ?_ ?_
  · rw [this]; exact Dvd.intro _ rfl
  · rw [this]; exact Dvd.intro_left _ rfl

theorem burnsideA315x_case_cyclic {X : Type} [Group X] {S B : Subgroup X}
    (hS : ¬ IsCyclic ↥S) (hH : IsCyclic ↥(B ⊔ S)) : False :=
  hS (burnsideA315x_cyclic_of_le le_sup_right hH)

theorem burnsideA315x_case_small {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (hH : Nat.card ↥(B ⊔ S) = 12 ∨ Nat.card ↥(B ⊔ S) = 24) : False := by
  obtain ⟨-, hcard⟩ := hc.sup_card
  rw [hSk] at hcard
  have hb := hc.odd
  have hk4 : k ≤ 4 := by
    by_contra h
    have h1 : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < Nat.card ↥B := Nat.card_pos
    rcases hH with h | h <;> rw [h] at hcard <;> nlinarith
  have h3 : Nat.card ↥B = 3 := by
    obtain ⟨j, hj⟩ := hb
    interval_cases k <;> rcases hH with h | h <;> rw [h] at hcard <;> omega
  exact hc.false_of_pow_three (k := 1) (by rw [h3]; rfl)

theorem burnsideA315x_case_A5 {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (e : ↥(B ⊔ S) ≃* alternatingGroup (Fin 5)) (hH : Nat.card ↥(B ⊔ S) = 60) : False := by
  obtain ⟨-, hcard⟩ := hc.sup_card
  rw [hSk, hH] at hcard
  have hb := hc.odd
  have hk4 : k ≤ 5 := by
    by_contra h
    have h1 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < Nat.card ↥B := Nat.card_pos
    nlinarith
  have h3 : Nat.card ↥B = 15 := by
    obtain ⟨j, hj⟩ := hb
    interval_cases k <;> omega
  obtain ⟨z, hzB, hz⟩ := hc.exists_order_mul (r := 3) (s := 5) Nat.prime_three (by norm_num)
    (by norm_num) (by rw [h3]; norm_num) (by rw [h3]; norm_num)
  exact burnsideA315x_alt_no_order e (r := 3) (s := 5) Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (⟨z, (le_sup_left : B ≤ B ⊔ S) hzB⟩ : ↥(B ⊔ S))
    (by rw [Subgroup.orderOf_mk, hz])


theorem burnsideA315x_case_ext {X : Type} [Group X] [Finite X] {S H : Subgroup X} (hSH : S ≤ H)
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k)
    (hS : ¬ IsCyclic ↥S) (P : Subgroup ↥H) [P.Normal] (hP : Nat.card ↥P = p ^ m)
    (hQ : IsCyclic (↥H ⧸ P)) : False := by
  let f : ↥(S.subgroupOf H) →* ↥H ⧸ P := (QuotientGroup.mk' P).comp (S.subgroupOf H).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxP : ((x : ↥H)) ∈ P := (QuotientGroup.eq_one_iff _).1 hx
    have h1 : orderOf (x : ↥H) ∣ p ^ m := by
      rw [← hP]
      have := orderOf_dvd_natCard (⟨(x : ↥H), hxP⟩ : ↥P)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (x : ↥H) ∣ 2 ^ k := by
      rw [← hSk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
      have := orderOf_dvd_natCard x
      rwa [← Subgroup.orderOf_coe] at this
    have hcop : Nat.Coprime (p ^ m) (2 ^ k) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 : orderOf (x : ↥H) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h4 : (x : ↥H) = 1 := orderOf_eq_one_iff.1 h3
    exact Subtype.ext h4
  have hc : IsCyclic ↥(S.subgroupOf H) := isCyclic_of_injective f hinj
  exact hS (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSH).surjective)


theorem burnsideA315x_rot_cyclic {X : Type} [Group X] {H : Subgroup X} {z : ℕ} [NeZero z]
    (e : ↥H ≃* DihedralGroup z) (T : Subgroup X) (hTH : T ≤ H)
    (h : ∀ t : X, ∀ ht : t ∈ T, ∃ i : ZMod z, e ⟨t, hTH ht⟩ = DihedralGroup.r i) :
    IsCyclic ↥T := by
  let f : ↥T →* DihedralGroup z := e.toMonoidHom.comp (Subgroup.inclusion hTH)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subgroup.inclusion_injective hTH (e.injective hab)
  have hrange : f.range ≤ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := h t.1 t.2
    have : f t = DihedralGroup.r i := hi
    rw [this]
    refine ⟨(i.val : ℤ), ?_⟩
    show DihedralGroup.r 1 ^ ((i.val : ℕ) : ℤ) = DihedralGroup.r i
    rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  haveI : IsCyclic ↥(Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)) := inferInstance
  have h1 : IsCyclic ↥f.range := burnsideA315x_cyclic_of_le hrange inferInstance
  exact isCyclic_of_surjective (MonoidHom.ofInjective hf).symm.toMonoidHom
    (MonoidHom.ofInjective hf).symm.surjective

theorem burnsideA315x_case_dihedral {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hk : 2 ≤ k) (hSk : Nat.card ↥S = 2 ^ k)
    (hSnc : ¬ IsCyclic ↥S) {z : ℕ} (e : ↥(B ⊔ S) ≃* DihedralGroup z) :
    IsCyclic ↥B ∧ Nat.card ↥B ∣ z ∧ 2 ∣ z ∧ ∃ s ∈ S, ∀ x ∈ B, s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨hle, hcard⟩ := hc.sup_card
  have hHz : Nat.card ↥(B ⊔ S) = 2 * z := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hHz
    exact (Nat.card_pos (α := ↥(B ⊔ S))).ne' hHz
  haveI : NeZero z := ⟨hz0⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hz : z = Nat.card ↥B * 2 ^ (k' + 1) := by
    have h1 : 2 * z = 2 * (Nat.card ↥B * 2 ^ (k' + 1)) := by
      rw [← hHz, hcard, hSk]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hrot : ∀ y : ↥(B ⊔ S), Odd (orderOf y) → ∃ i : ZMod z, e y = DihedralGroup.r i := by
    intro y hy
    rcases hey : e y with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h2 : orderOf (e y) = orderOf y := MulEquiv.orderOf_eq e y
      rw [hey, DihedralGroup.orderOf_sr] at h2
      rw [← h2] at hy
      exact absurd hy (by decide)
  have hBrot : ∀ t : X, ∀ ht : t ∈ B, ∃ i : ZMod z,
      e ⟨t, (le_sup_left : B ≤ B ⊔ S) ht⟩ = DihedralGroup.r i := by
    intro t ht
    refine hrot _ ?_
    have h1 : orderOf (⟨t, ht⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    have h2 : orderOf (⟨t, (le_sup_left : B ≤ B ⊔ S) ht⟩ : ↥(B ⊔ S)) = orderOf (⟨t, ht⟩ : ↥B) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [h2]
    exact Odd.of_dvd_nat hc.odd h1
  refine ⟨burnsideA315x_rot_cyclic e B le_sup_left hBrot, ⟨2 ^ (k' + 1), hz⟩, ?_, ?_⟩
  · rw [hz]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  · have hrefl : ∃ s : X, ∃ hs : s ∈ S, ∃ j : ZMod z, e ⟨s, hle hs⟩ = DihedralGroup.sr j := by
      by_contra hno
      push Not at hno
      apply hSnc
      refine burnsideA315x_rot_cyclic e S hle ?_
      intro t ht
      rcases hey : e ⟨t, hle ht⟩ with i | i
      · exact ⟨i, rfl⟩
      · exact absurd hey (hno t ht i)
    obtain ⟨s, hs, j, hsj⟩ := hrefl
    refine ⟨s, hs, fun b hb => ?_⟩
    obtain ⟨i, hi⟩ := hBrot b hb
    have key : (⟨s, hle hs⟩ : ↥(B ⊔ S)) * ⟨b, (le_sup_left : B ≤ B ⊔ S) hb⟩ * ⟨s, hle hs⟩⁻¹ =
        ⟨b, (le_sup_left : B ≤ B ⊔ S) hb⟩⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, hsj, hi, DihedralGroup.inv_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
    have := congrArg Subtype.val key
    simpa using this


theorem burnsideA315x_pow_two_pair {a i l : ℕ} (ha : 3 ≤ a) (h1 : a - 1 = 2 ^ i)
    (h2 : a + 1 = 2 ^ l) : a = 3 := by
  have key : ∀ n : ℕ, 2 ^ n = 1 ∨ 2 ^ n = 2 ∨ 4 ∣ 2 ^ n := by
    intro n
    rcases n with _ | _ | n
    · left; rfl
    · right; left; rfl
    · right; right
      exact ⟨2 ^ n, by ring⟩
  rcases key i with hi | hi | hi <;> rcases key l with hl | hl | hl <;> omega

theorem burnsideA315x_dvd_two_pow {N j k c p : ℕ} (hp : p.Prime) (hNp : ¬ p ∣ N)
    (h : N ∣ p ^ j * (2 ^ k * c)) : N ∣ 2 ^ k * c :=
  Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp).symm) h


theorem burnsideA315x_case_subfield {X Y : Type} [Group X] [Finite X] [Group Y]
    {S B : Subgroup X} (hc : burnsideA315x_Config X S B) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k)
    (e : ↥(B ⊔ S) ≃* Y) {p m c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hc12 : c = 1 ∨ c = 2) (hY : Nat.card Y * c = p ^ m * ((p ^ m) ^ 2 - 1))
    (hnc : ∀ u x : Y, orderOf u = p → (orderOf x).Prime → orderOf x ≠ p → Odd (orderOf x) →
      ¬ Commute u x) : False := by
  obtain ⟨hle, hcard⟩ := hc.sup_card
  have hHY : Nat.card ↥(B ⊔ S) = Nat.card Y := Nat.card_congr e.toEquiv
  rw [hSk] at hcard
  have hBY : Nat.card Y = Nat.card ↥B * 2 ^ k := by rw [← hHY, hcard]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpm : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hpY : p ∣ Nat.card Y * c := by
    rw [hY]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  have hpY' : p ∣ Nat.card Y := by
    rcases hc12 with rfl | rfl
    · simpa using hpY
    · rcases (Nat.Prime.dvd_mul hp).1 hpY with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
  have hpB : p ∣ Nat.card ↥B := by
    rw [hBY] at hpY'
    rcases (Nat.Prime.dvd_mul hp).1 hpY' with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) p hpB
  let ι : ↥B →* Y := e.toMonoidHom.comp (Subgroup.inclusion le_sup_left)
  have hι : Function.Injective ι := fun a b hab =>
    Subgroup.inclusion_injective le_sup_left (e.injective hab)
  have hall : ∀ {r : ℕ}, r.Prime → r ∣ Nat.card ↥B → r = p := by
    intro r hr hrB
    by_contra hrp
    rcases hc.cases with hab | ⟨q, hq, hBq⟩
    · haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
      have hcomm : Commute u x := hab.is_comm.comm u x
      refine hnc (ι u) (ι x) ?_ ?_ ?_ ?_ (hcomm.map ι)
      · rw [orderOf_injective ι hι u, hu]
      · rw [orderOf_injective ι hι x, hx]; exact hr
      · rw [orderOf_injective ι hι x, hx]; exact hrp
      · rw [orderOf_injective ι hι x, hx]; exact Odd.of_dvd_nat hc.odd hrB
    · haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨j, hj⟩ := hBq.exists_card_eq
      rw [hj] at hpB hrB
      have h1 := (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hpB)
      have h2 := (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hrB)
      exact hrp (h2.trans h1.symm)
  obtain ⟨j, hBp⟩ : ∃ j : ℕ, Nat.card ↥B = p ^ j :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun hd hdB => hall hd hdB)⟩
  set N' := (p ^ m) ^ 2 - 1 with hN'
  have hNp : ¬ p ∣ N' := by
    intro h
    have h1 : (p ^ m) ^ 2 = N' + 1 := by
      have : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h2 : p ∣ (p ^ m) ^ 2 := Dvd.dvd.pow (dvd_pow_self p (by omega)) (by norm_num)
    rw [h1] at h2
    have := (Nat.dvd_add_right h).1 h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hdiv : N' ∣ p ^ j * (2 ^ k * c) := by
    have : N' ∣ p ^ m * N' := Dvd.intro_left _ rfl
    rw [← hY, hBY, mul_assoc, hBp] at this
    exact this
  have hdiv2 := burnsideA315x_dvd_two_pow hp hNp hdiv
  have hdiv3 : N' ∣ 2 ^ (k + 1) := by
    refine hdiv2.trans ?_
    rcases hc12 with rfl | rfl
    · exact ⟨2, by ring⟩
    · exact ⟨1, by ring⟩
  have hfac : N' = (p ^ m - 1) * (p ^ m + 1) := by
    rw [hN']
    have := Nat.sq_sub_sq (p ^ m) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    ((Dvd.intro _ hfac.symm : (p ^ m - 1) ∣ N').trans hdiv3)
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    ((Dvd.intro_left _ hfac.symm : (p ^ m + 1) ∣ N').trans hdiv3)
  have h3 : p ^ m = 3 := burnsideA315x_pow_two_pair hpm hi hl
  have hp3' : p = 3 := by
    have : p ∣ 3 := h3 ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
  rw [hp3'] at hBp
  exact hc.false_of_pow_three hBp


theorem burnsideA315x_psl2_no_commute {p m : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (u x : CFSG.GorensteinWalter.PSL2 (GaloisField p m)) (hu : orderOf u = p)
    (hx : (orderOf x).Prime) (hxp : orderOf x ≠ p) : ¬ Commute u x := by
  intro hcomm
  haveI : Fact (orderOf x).Prime := ⟨hx⟩
  exact CFSG.GorensteinWalter.psl2_no_commuting_distinct_prime_order (F := GaloisField p m)
    (r := p) (f := m) (p := orderOf x) (GaloisField.card p m (by omega)) hxp hu rfl hcomm

theorem burnsideA315x_case_psl {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k) {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (e : ↥(B ⊔ S) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) : False := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (by omega)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
    ⟨p, m, Fact.out, hpodd, hm, hK⟩
  have hcard := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p m) hodd
  rw [hK] at hcard
  have heven : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
    have h1 : Odd ((p ^ m) ^ 2) := (hpodd.pow).pow
    have h2 : Even ((p ^ m) ^ 2 - 1) := Nat.Odd.sub_odd h1 odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h2) _
  refine burnsideA315x_case_subfield hc hSk e (c := 2) (Fact.out : p.Prime) hp2 hm (Or.inr rfl)
    ?_ ?_
  · show Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField p m)) * 2 = _
    rw [hcard]
    exact Nat.div_mul_cancel heven
  · intro u x hu hx hxp _
    exact burnsideA315x_psl2_no_commute hm u x hu hx hxp

theorem burnsideA315x_case_pgl {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) {k : ℕ} (hSk : Nat.card ↥S = 2 ^ k) {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (e : ↥(B ⊔ S) ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) : False := by
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (by omega)
  have hcard := CFSG.GorensteinWalter.pgl2_card_formula (GaloisField p m)
  rw [hK] at hcard
  refine burnsideA315x_case_subfield hc hSk e (c := 1) (Fact.out : p.Prime) hp2 hm (Or.inl rfl)
    ?_ ?_
  · show Nat.card (CFSG.GorensteinWalter.PGL2 (GaloisField p m)) * 1 = _
    rw [hcard, mul_one]
  · intro u x hu hx hxp hxodd
    intro hcomm
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    obtain ⟨a, ha⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd
      (g := u) (n := orderOf u) (by rw [hu]; exact hpodd) (pow_orderOf_eq_one u)
    obtain ⟨b, hb⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd
      (g := x) (n := orderOf x) hxodd (pow_orderOf_eq_one x)
    have hinj := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2)
      (R := GaloisField p m)
    have hab : Commute a b := by
      apply hinj
      rw [map_mul, map_mul, ha, hb]
      exact hcomm
    have hoa : orderOf a = orderOf u := by
      rw [← ha]
      exact (orderOf_injective _ hinj a).symm
    have hob : orderOf b = orderOf x := by
      rw [← hb]
      exact (orderOf_injective _ hinj b).symm
    refine burnsideA315x_psl2_no_commute hm a b (hoa.trans hu) ?_ ?_ hab
    · rw [hob]; exact hx
    · rw [hob]; exact hxp


open scoped Pointwise in
theorem burnsideA315x_Config.map {X Y : Type} [Group X] [Group Y] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) (e : X ≃* Y) :
    burnsideA315x_Config Y (S.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  have eB : ↥B ≃* ↥(B.map e.toMonoidHom) := B.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_map_mulEquiv e hc.sylow, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr eB.toEquiv]
    exact hc.odd
  · intro hp
    exact hc.not3 (hp.of_equiv eB.symm)
  · rcases hc.cases with hab | ⟨r, hr, hBr⟩
    · left
      refine ⟨⟨fun a b => ?_⟩⟩
      apply eB.symm.injective
      rw [map_mul, map_mul]
      exact hab.is_comm.comm _ _
    · right
      exact ⟨r, hr, hBr.of_equiv eB⟩
  · exact burnsideA315x_map_permute e.toMonoidHom hc.perm

theorem burnsideA315x_l2_core {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he1 : 1 ≤ e)
    {S B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))}
    (hc : burnsideA315x_Config _ S B) :
    IsCyclic ↥B ∧ (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε ((p ^ e : ℕ) : ℤ) ∧
      ((Nat.card ↥B : ℕ) : ℤ) ∣ ((p ^ e : ℕ) : ℤ) - ε) ∧
      ∃ s ∈ S, ∀ x ∈ B, s * x * s⁻¹ = x⁻¹ := by
  have hq : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  obtain ⟨⟨m, hm, hSc⟩, hSnc⟩ :=
    burnsideA315x_sylow_facts (F := GaloisField p e) (Fact.out) hp2 he1 hq hc.sylow
  have hk : 2 ≤ m + 1 := by omega
  obtain ⟨hle, hcard⟩ := hc.sup_card
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hSH : 2 ∣ Nat.card ↥(B ⊔ S) := by
    have h1 : Nat.card ↥S ∣ Nat.card ↥(B ⊔ S) := Subgroup.card_dvd_of_le hle
    rw [hSc] at h1
    exact (dvd_pow_self 2 (by omega)).trans h1
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds p e he1 (B ⊔ S) with
    ⟨-, m', -, hcard'⟩ | ⟨hcyc, -⟩ | ⟨z, hz, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ |
      ⟨m', t, P, hP, -, hPc, hQc, -, -, -⟩ | ⟨m', hm', ⟨e'⟩⟩ | ⟨m', hm', ⟨e'⟩⟩
  · exfalso
    rw [hcard'] at hSH
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1
      (Nat.prime_two.dvd_of_dvd_pow hSH)).symm
  · exact (burnsideA315x_case_cyclic hSnc hcyc).elim
  ·
    obtain ⟨hBcyc, hBdvd, h2z, s, hs, hinv⟩ :=
      burnsideA315x_case_dihedral hc hk hSc hSnc e'
    refine ⟨hBcyc, ?_, s, hs, hinv⟩
    have hqodd : Odd (p ^ e) := hpodd.pow
    obtain ⟨t, ht⟩ := hqodd
    have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
      rw [ht, Nat.add_sub_cancel]
      exact Nat.gcd_eq_left (Dvd.intro t rfl)
    rw [hg] at hz
    obtain ⟨z', hz'⟩ := h2z
    rcases hz with ⟨c, hc'⟩ | ⟨c, hc'⟩
    ·
      refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · have h4 : (p ^ e + 1) = 4 * (z' * c) := by
          have : (p ^ e + 1) = 2 * ((p ^ e + 1) / 2) := by omega
          rw [this, hc', hz']
          ring
        rw [Int.ModEq]
        omega
      · have hdvd : Nat.card ↥B ∣ p ^ e + 1 := by
          refine hBdvd.trans ⟨2 * c, ?_⟩
          have : (p ^ e + 1) = 2 * ((p ^ e + 1) / 2) := by omega
          rw [this, hc']
          ring
        have := Int.natCast_dvd_natCast.2 hdvd
        push_cast at this ⊢
        simpa using this
    · refine ⟨1, Or.inl rfl, ?_, ?_⟩
      · have h4 : (p ^ e - 1) = 4 * (z' * c) := by
          have : (p ^ e - 1) = 2 * ((p ^ e - 1) / 2) := by omega
          rw [this, hc', hz']
          ring
        rw [Int.ModEq]
        omega
      · have hdvd : Nat.card ↥B ∣ p ^ e - 1 := by
          refine hBdvd.trans ⟨2 * c, ?_⟩
          have : (p ^ e - 1) = 2 * ((p ^ e - 1) / 2) := by omega
          rw [this, hc']
          ring
        have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        have := Int.natCast_dvd_natCast.2 hdvd
        push_cast [Nat.cast_sub h1] at this ⊢
        exact this
  · exfalso
    refine burnsideA315x_case_small hc hk hSc (Or.inl ?_)
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · exfalso
    refine burnsideA315x_case_small hc hk hSc (Or.inr ?_)
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  · exfalso
    refine burnsideA315x_case_A5 hc hk hSc e' ?_
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · exfalso
    haveI := hP
    exact burnsideA315x_case_ext le_sup_right (Fact.out : p.Prime) hp2 hSc hSnc P hPc hQc
  · exfalso
    have hm0 : 1 ≤ m' := Nat.pos_of_dvd_of_pos hm' (by omega)
    exact burnsideA315x_case_psl hc hSc hp2 hm0 e'
  · exfalso
    have hm0 : 1 ≤ m' := by
      have := Nat.pos_of_dvd_of_pos hm' (by omega)
      omega
    exact burnsideA315x_case_pgl hc hSc hp2 hm0 e'


theorem burnsideA315x_quot_abelian {G Q : Type} [Group G] [Group Q] [Finite G] {r : ℕ}
    [Fact r.Prime] (π : G →* Q) (hπ : Function.Surjective π)
    (hab : ∀ R : Subgroup G, IsPGroup r ↥R → IsMulCommutative ↥R) (R : Subgroup Q)
    (hR : IsPGroup r ↥R) : IsMulCommutative ↥R := by
  haveI : Finite Q := Finite.of_surjective _ hπ
  obtain ⟨P', hRP'⟩ := hR.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ r P'
  have hPS : (P' : Subgroup Q) = (S : Subgroup G).map π := by
    rw [← hS, Sylow.coe_mapSurjective]
  have hSab := hab (S : Subgroup G) S.isPGroup'
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : (x : Q) ∈ (S : Subgroup G).map π := hPS ▸ hRP' x.2
  have hy : (y : Q) ∈ (S : Subgroup G).map π := hPS ▸ hRP' y.2
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val (hSab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)


open CFSG.Quasithin.F134.LieU3 CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in


end CFSG.ASVolI
