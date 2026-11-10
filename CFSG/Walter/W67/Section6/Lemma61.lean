module

public import CFSG.Walter.W67.Section6.Basic
public import CFSG.Walter.W67.Section6.Core61
public import CFSG.Walter.W67.Section6.R1512

public section

namespace CFSG.Walter.W67

namespace Sec6

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem gData_of_sylowData {L : Subgroup G} {hL : JRGroup L} {r : ℕ} [Fact r.Prime]
    {P C W : Subgroup L} (hD : SylowData hL r P C W)
    (hPc : Nat.card P = r ^ (Nat.card L).factorization r) (hP : P ≠ ⊥)
    {w : L} (hw : w ∈ W) {p : ℕ} (hp : hL.q = 5 → p = 5) :
    GData L (w : G) p r (P.map L.subtype) (C.map L.subtype) (W.map L.subtype) where
  C_le := Subgroup.map_subtype_le C
  W_le := Subgroup.map_subtype_le W
  P_le_C := Subgroup.map_mono hD.P_le_C
  P_card := by rw [Subgroup.card_map_of_injective L.subtype_injective]; exact hPc
  P_ne := fun h => hP ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h)
  C_comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hD.C_comm a ha b hb)
  C_hall := by
    rw [show (C.map L.subtype).subgroupOf L = C from
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective C,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact hD.C_hall
  C_cent := by
    rintro _ ⟨c, hc, rfl⟩ hc1
    have hc1' : c ≠ 1 := fun h => hc1 (by simp [h])
    rw [← hD.C_cent c hc hc1', JT.map_centralizer_singleton_of_injective _ L.subtype_injective,
      Subgroup.range_subtype]
  CW_inf := by rw [← Subgroup.map_inf_eq _ _ _ L.subtype_injective, hD.CW_inf, Subgroup.map_bot]
  CW_sup := by
    rw [← Subgroup.map_sup, hD.CW_sup, JT.map_normalizer_of_injective _ L.subtype_injective,
      Subgroup.range_subtype]
  C_norm := by
    have h1 := JT.map_normalizer_of_injective L.subtype L.subtype_injective P
    have h2 := JT.map_normalizer_of_injective L.subtype L.subtype_injective C
    rw [Subgroup.range_subtype] at h1 h2
    rw [← h1]
    exact (Subgroup.map_mono hD.C_norm).trans (h2.le.trans inf_le_right)
  W_cyc := by
    have := hD.W_cyc
    exact isCyclic_of_surjective (L.subtype.subgroupMap W) (L.subtype.subgroupMap_surjective W)
  W_card := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    rcases hD.W_card with h | ⟨h5, h11, h10⟩
    · exact Or.inl h
    · exact Or.inr ⟨hp h5, h11, h10⟩
  J_mem := ⟨w, hw, rfl⟩

theorem exists_sylowData
    {L : Type} [Group L] [Finite L] (hJ : JFacts) (hR : RFacts)
    (hL : JRGroup L) (hns : ¬ Group.IsSolvable L) {r : ℕ} [Fact r.Prime]
    (hr : ¬ r ∣ hL.q * (hL.q ^ 2 - 1)) {P : Subgroup L}
    (hPc : Nat.card P = r ^ (Nat.card L).factorization r) (hP : P ≠ ⊥) :
    ∃ C W : Subgroup L, SylowData hL r P C W := by
  have hq3 : 3 ≤ hL.q := by
    have hp := (Fact.out : hL.p.Prime).two_le
    have hp2 := hL.p_ne_two
    have : hL.p ≤ hL.q := Nat.le_self_pow hL.f_pos.ne' _
    omega
  by_cases h5 : hL.q = 5
  · rw [h5] at hr
    exact exists_sylowData_of_J hJ hL h5 (by norm_num at hr ⊢; exact hr) hPc hP
  · by_cases h3 : hL.q = 3
    · exact exists_sylowData_of_R3 hR hL h3 hns hr hPc hP
    · exact exists_sylowData_of_R hR hL h5 (by omega) hr hPc hP

theorem SylowData.exists_involution {L : Type} [Group L] [Finite L] {hL : JRGroup L} {r : ℕ}
    {P C W : Subgroup L} (hD : SylowData hL r P C W) : ∃ w ∈ W, orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card W := by rcases hD.W_card with h | ⟨-, -, h⟩ <;> rw [h] <;> norm_num
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2
  exact ⟨w, hw, by rwa [Subgroup.orderOf_mk] at hw2⟩

variable (s : Std G)

theorem card_K'_dvd
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) {K' : Subgroup G}
    (hK' : IsJRSubgroup (s.L X) s.J K' s.p (s.f / Nat.card X)) :
    Nat.card K' ∣ s.q * (s.q ^ 2 - 1) := by
  obtain ⟨eK'⟩ := hK'.iso
  have hpos := f_div_pos s hXE hX
  have hFcard : Nat.card (GaloisField s.p (s.f / Nat.card X)) = s.p ^ (s.f / Nat.card X) :=
    GaloisField.card _ _ hpos.ne'
  rw [Nat.card_congr eK'.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _
    ⟨s.p, s.f / Nat.card X, Fact.out, s.odd_p, hpos, hFcard⟩, hFcard]
  refine (Nat.div_dvd_of_dvd ?_).trans (q_mul_dvd s hXE hX)
  have hq : Odd (s.p ^ (s.f / Nat.card X)) := (s.odd_p).pow
  have : Even ((s.p ^ (s.f / Nat.card X)) ^ 2 - 1) := Nat.Odd.sub_odd hq.pow odd_one
  exact (this.mul_left _).two_dvd

theorem E_le_normalizer_K'
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) {K' : Subgroup G}
    (hK' : IsJRSubgroup (s.L X) s.J K' s.p (s.f / Nat.card X))
    (hK'X : 3 < s.p ^ (s.f / Nat.card X) → K' = s.KX X) :
    s.fr.E ≤ Subgroup.normalizer (K' : Set G) := by
  by_cases h3 : 3 < s.p ^ (s.f / Nat.card X)
  · rw [hK'X h3]
    intro e he
    exact mem_normalizer_inf (s.fr.E_le_normalizer_K he)
      (Huppert.normalizer_le_normalizer_centralizer X (E_le_normalizer s hXE he))
  · have hp3 : 3 ≤ s.p := by
      have := (Fact.out : s.p.Prime).two_le
      have := s.p_ne_two
      omega
    have hpos := f_div_pos s hXE hX
    have h1 : s.f / Nat.card X = 1 := by
      by_contra h1
      have h2 : s.p ^ 2 ≤ s.p ^ (s.f / Nat.card X) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    obtain ⟨c, hc⟩ := card_dvd_f s hXE hX
    have hcX : s.f = Nat.card X := by
      rw [hc, Nat.mul_div_cancel_left _ Nat.card_pos] at h1
      rw [hc, h1, mul_one]
    have hXeq : X = s.fr.E := by
      apply Subgroup.eq_of_le_of_card_ge hXE
      rw [← hcX]
      exact Nat.le_of_dvd s.f_pos (card_dvd_f s le_rfl s.E_ne_bot)
    have hK'L : K' ≤ s.L X := hK'.K_le.trans inf_le_left
    intro e he
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have heX : e ∈ X := by rw [hXeq]; exact he
    exact (Subgroup.mem_centralizer_iff.mp (L_le_centralizer s hXE hX (hK'L hk)) e heX).symm

theorem exists_data
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {r : ℕ} [Fact r.Prime] (hrσ : r ∈ s.fr.σ) {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (hns : ¬ Group.IsSolvable (Subgroup.normalizer (X : Set G)))
    (hrL : r ∣ Nat.card (s.L X)) :
    ∃ P C W : Subgroup G, GData (s.L X) s.J s.p r P C W ∧
      s.fr.E ≤ Subgroup.normalizer (P : Set G) ∧ s.fr.E ≤ Subgroup.centralizer (W : Set G) := by
  obtain ⟨K', hK', hK'X, hL, hLp, hLf, hLJ, -⟩ := exists_jrGroup s hXE hX
  have hq := jrGroup_q s hL hLp hLf
  have hnsL : ¬ Group.IsSolvable (s.L X) := by
    intro hsol
    apply hns
    rw [normalizer_eq s hXE hX]
    exact isSolvable_sup_of_comm (E_le_normalizer_L s hXE hX) (E_comm s) hsol
  have hrq : ¬ r ∣ hL.q * (hL.q ^ 2 - 1) := by
    rw [hq]
    exact fun h => not_dvd_q_mul s h41 h56 hJ hR hrσ (h.trans (q_mul_dvd s hXE hX))
  have hp5 : hL.q = 5 → s.p = 5 := by
    intro h5
    rw [hq] at h5
    have hdvd : s.p ∣ 5 := h5 ▸ dvd_pow_self s.p (f_div_pos s hXE hX).ne'
    exact (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hdvd
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r (s.L X)))
  have hQc : Nat.card (Q : Subgroup (s.L X)) = r ^ (Nat.card (s.L X)).factorization r :=
    Sylow.card_eq_multiplicity Q
  have hQ : (Q : Subgroup (s.L X)) ≠ ⊥ := by
    intro h
    have hk := (Fact.out : r.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hrL
    rw [h, Subgroup.card_bot] at hQc
    have := Nat.one_lt_pow hk.ne' (Fact.out : r.Prime).one_lt
    omega
  obtain ⟨C₀, W₀, hD₀⟩ := exists_sylowData hJ hR hL hnsL hrq hQc hQ
  obtain ⟨w, hwW, hw2⟩ := hD₀.exists_involution
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : s.L X, ℓ * w * ℓ⁻¹ = hL.J := by
    have hconj : IsConj w hL.J := by
      by_cases h5 : hL.q = 5
      · exact (hJ _ hL h5).1.2.2 w hL.J hw2 hL.orderOf_J
      · exact (hR _ hL h5).2.1.2 w hL.J hw2 hL.orderOf_J
    exact isConj_iff.mp hconj
  have hD₁ := (gData_of_sylowData hD₀ hQc hQ hwW hp5).cj ℓ.2
  have hJeq : (ℓ : G) * (w : G) * (ℓ : G)⁻¹ = s.J := by
    rw [← hLJ, ← hℓ]
    rfl
  rw [hJeq] at hD₁
  have hK'L : K' ≤ s.L X := hK'.K_le.trans inf_le_left
  have hK'J : K' ≤ Subgroup.centralizer ({s.J} : Set G) := hK'.K_le.trans inf_le_right
  have hcopK : Nat.Coprime (Nat.card K') (Nat.card s.fr.E) :=
    Nat.Coprime.coprime_dvd_left (card_K'_dvd s hXE hX hK') (coprime_q_mul_E s h41 h56 hJ hR)
  have hcopW : Nat.Coprime (Nat.card (Sec6.cj (ℓ : G) (W₀.map (s.L X).subtype)))
      (Nat.card s.fr.E) := by
    have hEodd : Odd (Nat.card s.fr.E) := s.fr.odd_card_E
    have h3 := not_three_dvd_card_E s h41 h56 hJ hR
    rcases hD₁.W_card with h | ⟨hp5', -, h⟩
    · rw [h, show (6 : ℕ) = 2 * 3 from rfl]
      exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hEodd,
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
    · rw [h, show (10 : ℕ) = 2 * 5 from rfl]
      exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hEodd,
        (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (prop_5_2' s hJ hR hp5')⟩
  obtain ⟨k, hkK, hEP, hEW⟩ := exists_adjust (E_le_normalizer_L s hXE hX)
    (L_inf_E s h41 h56 hJ hR hXE hX) s.orderOf_J s.fr.E_le_H hK'.centralizer_eq hK'J
    hK'.J_not_mem (E_le_normalizer_K' s hXE hX hK' hK'X) hcopK hcopW hD₁
  have hD₂ := hD₁.cj ((s.L X).inv_mem (hK'L hkK))
  have hJk : k⁻¹ * s.J * k⁻¹⁻¹ = s.J := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hK'J hkK)
    rw [inv_inv]
    calc k⁻¹ * s.J * k = k⁻¹ * (k * s.J) := by rw [mul_assoc, hc]
      _ = s.J := by group
  rw [hJk] at hD₂
  refine ⟨_, _, _, hD₂, hEP, fun e he => ?_⟩
  exact mem_centralizer_of_odd_of_cyclic hD₂.W_cyc hD₂.totient_dvd (hEW he)
    (odd_orderOf_of_mem_oddPart he)


theorem exists_sylow
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {r : ℕ} [Fact r.Prime] (hrσ : r ∈ s.fr.σ) {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (hns : ¬ Group.IsSolvable (Subgroup.normalizer (X : Set G))) :
    ∃ P₀ P₁ : Subgroup G, P₀ ≤ s.fr.E ∧ Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r ∧
      P₁ ≤ s.L X ∧ Nat.card P₁ = r ^ (Nat.card (s.L X)).factorization r ∧
      s.fr.E ≤ Subgroup.normalizer (P₁ : Set G) ∧
      (P₁ ≠ ⊥ → ∃ C W : Subgroup G, GData (s.L X) s.J s.p r P₁ C W ∧
        s.fr.E ≤ Subgroup.centralizer (W : Set G)) := by
  obtain ⟨P₁, hP₁L, hP₁c, hEP₁, hdata⟩ : ∃ P₁ : Subgroup G, P₁ ≤ s.L X ∧
      Nat.card P₁ = r ^ (Nat.card (s.L X)).factorization r ∧
      s.fr.E ≤ Subgroup.normalizer (P₁ : Set G) ∧
      (P₁ ≠ ⊥ → ∃ C W : Subgroup G, GData (s.L X) s.J s.p r P₁ C W ∧
        s.fr.E ≤ Subgroup.centralizer (W : Set G)) := by
    by_cases hrL : r ∣ Nat.card (s.L X)
    · obtain ⟨P₁, C, W, hD, hEP, hEW⟩ := exists_data s h41 h56 hJ hR hrσ hXE hX hns hrL
      exact ⟨P₁, hD.P_le, hD.P_card, hEP, fun _ => ⟨C, W, hD, hEW⟩⟩
    · refine ⟨⊥, bot_le, ?_, ?_, fun h => absurd rfl h⟩
      · rw [Subgroup.card_bot, Nat.factorization_eq_zero_of_not_dvd hrL, pow_zero]
      · rw [Subgroup.normalizer_eq_top]
        exact le_top
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow r s.fr.E))
  refine ⟨(Q₀ : Subgroup s.fr.E).map s.fr.E.subtype, P₁, Subgroup.map_subtype_le _, ?_, hP₁L,
    hP₁c, hEP₁, hdata⟩
  rw [Subgroup.card_map_of_injective s.fr.E.subtype_injective, Sylow.card_eq_multiplicity]

theorem exists_P
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {r : ℕ} [Fact r.Prime] (hrσ : r ∈ s.fr.σ) {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (hns : ¬ Group.IsSolvable (Subgroup.normalizer (X : Set G))) :
    ∃ P₀ P₁ : Subgroup G, P₀ ≤ s.fr.E ∧ Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r ∧
      P₁ ≤ s.L X ∧ Nat.card P₁ = r ^ (Nat.card (s.L X)).factorization r ∧
      s.fr.E ≤ Subgroup.normalizer (P₁ : Set G) ∧
      (P₁ ≠ ⊥ → ∃ C W : Subgroup G, GData (s.L X) s.J s.p r P₁ C W ∧
        s.fr.E ≤ Subgroup.centralizer (W : Set G)) ∧
      (P₀ ⊔ P₁) ⊓ s.fr.E = P₀ ∧ (P₀ ⊔ P₁) ⊓ s.L X = P₁ ∧
      (P₀ ⊔ P₁) ⊓ Subgroup.centralizer ({s.J} : Set G) = P₀ ∧
      Nat.card ↥(P₀ ⊔ P₁) = r ^ (Nat.card (Subgroup.normalizer (X : Set G))).factorization r := by
  obtain ⟨P₀, P₁, hP₀E, hP₀c, hP₁L, hP₁c, hEP₁, hdata⟩ :=
    exists_sylow s h41 h56 hJ hR hrσ hXE hX hns
  have hrp : r.Prime := Fact.out
  have hLE := L_inf_E s h41 h56 hJ hR hXE hX
  have hEJ : s.fr.E ≤ Subgroup.centralizer ({s.J} : Set G) := s.fr.E_le_H
  have hrodd : Odd r := s.fr.odd_card_E.of_dvd_nat ((mem_sigma_iff s).mp hrσ).2
  obtain ⟨K', hK', -, -⟩ := exists_jrGroup s hXE hX
  have hrK' : ¬ r ∣ Nat.card K' := fun h =>
    not_dvd_q_mul s h41 h56 hJ hR hrσ (h.trans (card_K'_dvd s hXE hX hK'))
  have hP₀N : P₀ ≤ Subgroup.normalizer (P₁ : Set G) := hP₀E.trans hEP₁
  have hmem : ∀ x ∈ P₀ ⊔ P₁, ∃ b ∈ P₁, ∃ a ∈ P₀, b * a = x := fun x hx =>
    (mem_sup_iff_of_le_normalizer hP₀N).mp (by rwa [sup_comm] at hx)
  have hPE : (P₀ ⊔ P₁) ⊓ s.fr.E = P₀ := by
    apply le_antisymm _ (le_inf le_sup_left hP₀E)
    intro x hx
    obtain ⟨hxP, hxE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨b, hb, a, ha, rfl⟩ := hmem x hxP
    have hbE : b ∈ s.fr.E := by
      have e : b = b * a * a⁻¹ := by group
      rw [e]
      exact s.fr.E.mul_mem hxE (s.fr.E.inv_mem (hP₀E ha))
    have hb1 : b = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hP₁L hb, hbE⟩
      rwa [hLE, Subgroup.mem_bot] at this
    rw [hb1, one_mul]
    exact ha
  have hPL : (P₀ ⊔ P₁) ⊓ s.L X = P₁ := by
    apply le_antisymm _ (le_inf le_sup_right hP₁L)
    intro x hx
    obtain ⟨hxP, hxL⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨b, hb, a, ha, rfl⟩ := hmem x hxP
    have haL : a ∈ s.L X := by
      have e : a = b⁻¹ * (b * a) := by group
      rw [e]
      exact (s.L X).mul_mem ((s.L X).inv_mem (hP₁L hb)) hxL
    have ha1 : a = 1 := by
      have := Subgroup.mem_inf.mpr ⟨haL, hP₀E ha⟩
      rwa [hLE, Subgroup.mem_bot] at this
    rw [ha1, mul_one]
    exact hb
  have hPJ : (P₀ ⊔ P₁) ⊓ Subgroup.centralizer ({s.J} : Set G) = P₀ := by
    apply le_antisymm _ (le_inf le_sup_left (hP₀E.trans hEJ))
    intro x hx
    obtain ⟨hxP, hxJ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨b, hb, a, ha, rfl⟩ := hmem x hxP
    have hbJ : b ∈ Subgroup.centralizer ({s.J} : Set G) := by
      have e : b = b * a * a⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hxJ (Subgroup.inv_mem _ (hEJ (hP₀E ha)))
    have hbo : orderOf b ∣ r ^ (Nat.card (s.L X)).factorization r :=
      hP₁c ▸ Subgroup.orderOf_dvd_natCard P₁ hb
    have hbK : b ∈ K' := mem_of_odd_of_mem_zpowers_sup' s.orderOf_J
      (hK'.K_le.trans inf_le_right) hK'.J_not_mem
      (hK'.centralizer_eq ▸ Subgroup.mem_inf.mpr ⟨hP₁L hb, hbJ⟩)
      ((hrodd.pow).of_dvd_nat hbo)
    have hb1 : b = 1 := by
      have hcop : Nat.Coprime (r ^ (Nat.card (s.L X)).factorization r) (Nat.card K') :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hrp).mpr hrK')
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hbo hcop) (Subgroup.orderOf_dvd_natCard K' hbK))
    rw [hb1, one_mul]
    exact ha
  have hPcard : Nat.card ↥(P₀ ⊔ P₁) =
      r ^ (Nat.card (Subgroup.normalizer (X : Set G))).factorization r := by
    have hP₁P₀ : P₁ ⊓ P₀ = ⊥ := eq_bot_iff.mpr ((inf_le_inf hP₁L hP₀E).trans hLE.le)
    rw [sup_comm, card_sup_of_inf_eq_bot hP₀N hP₁P₀, hP₀c, hP₁c, ← pow_add,
      card_normalizer s h41 h56 hJ hR hXE hX,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, add_comm]
  exact ⟨P₀, P₁, hP₀E, hP₀c, hP₁L, hP₁c, hEP₁, hdata, hPE, hPL, hPJ, hPcard⟩

end Sec6

open Sec6


end CFSG.Walter.W67
