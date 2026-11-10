module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonInputs
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonAut
import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonHooksEng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem conj_mem_OCW {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G)) {x : G}
    (hx : x ∈ OCW W) : g * x * g⁻¹ ∈ OCW W := by
  have h := normalizer_le_normalizer_OCW W hg
  exact (Subgroup.mem_normalizer_iff.mp h x).mp hx

theorem conj_mem_MGrp {p f : ℕ} [Fact p.Prime] (hΩ : HypOmegaMod p f Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ MGrp Ω W) :
    g * x * g⁻¹ ∈ MGrp Ω W := by
  refine Subgroup.iSup_induction (C := fun x => g * x * g⁻¹ ∈ MGrp Ω W)
    (fun R : Subgroup G => ⨆ (_ : R ∈ DSet Ω W), R) hx ?_ (by simp) ?_
  · intro R y hy
    refine Subgroup.iSup_induction (C := fun x => g * x * g⁻¹ ∈ MGrp Ω W)
      (fun _ : R ∈ DSet Ω W => R) hy ?_ (by simp) ?_
    · intro hR z hz
      exact le_MGrp_of_mem_D (conjSub_mem_D hΩ hR hg) (conj_mem_conjSub hz)
    · intro x y hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
  · intro x y hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy

theorem conj_mem_MGrp_sup {p f : ℕ} [Fact p.Prime] (hΩ : HypOmegaMod p f Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ MGrp Ω W ⊔ OCW W) :
    g * x * g⁻¹ ∈ MGrp Ω W ⊔ OCW W := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_left (conj_mem_MGrp hΩ hg hx)
    · exact Subgroup.mem_sup_right (conj_mem_OCW hg hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

@[expose] noncomputable def conjQ {p f : ℕ} [Fact p.Prime] (hΩ : HypOmegaMod p f Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) : ↥(muGroup Ω W) ≃* ↥(muGroup Ω W) where
  toFun q := ⟨piG W g * q.1 * (piG W g)⁻¹, by
    obtain ⟨m, hm, hqm⟩ := mem_muGroup_iff.mp q.2
    have hmN := MGrp_sup_le_normalizer Ω W hm
    rw [hqm, ← piG_inv hg, ← piG_mul hg hmN, ← piG_mul (Subgroup.mul_mem _ hg hmN)
      (Subgroup.inv_mem _ hg)]
    exact piG_mem_muGroup (conj_mem_MGrp_sup hΩ hg hm)⟩
  invFun q := ⟨(piG W g)⁻¹ * q.1 * piG W g, by
    obtain ⟨m, hm, hqm⟩ := mem_muGroup_iff.mp q.2
    have hmN := MGrp_sup_le_normalizer Ω W hm
    have hg' : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hg
    have := piG_mem_muGroup (conj_mem_MGrp_sup hΩ hg' hm)
    rw [piG_mul (Subgroup.mul_mem _ hg' hmN) (Subgroup.inv_mem _ hg'), piG_mul hg' hmN,
      piG_inv hg', piG_inv hg, inv_inv] at this
    rw [hqm]
    exact this⟩
  left_inv q := Subtype.ext (by
    show (piG W g)⁻¹ * (piG W g * q.1 * (piG W g)⁻¹) * piG W g = q.1
    group)
  right_inv q := Subtype.ext (by
    show piG W g * ((piG W g)⁻¹ * q.1 * piG W g) * (piG W g)⁻¹ = q.1
    group)
  map_mul' x y := Subtype.ext (by
    show piG W g * (x.1 * y.1) * (piG W g)⁻¹ = (piG W g * x.1 * (piG W g)⁻¹) *
      (piG W g * y.1 * (piG W g)⁻¹)
    group)

theorem conjQ_apply {p f : ℕ} [Fact p.Prime] (hΩ : HypOmegaMod p f Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (q : ↥(muGroup Ω W)) :
    ((conjQ hΩ hg q : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) = piG W g * q.1 * (piG W g)⁻¹ := rfl

section Fixed

variable [Finite G] {p f : ℕ} [Fact p.Prime]

omit [Finite G] in
theorem normalizer_inf_normalizer_conj {K : Subgroup G} {a : G} (haK : conjSub a K = K)
    (haN : a ∈ Subgroup.normalizer (W : Set G)) :
    a ∈ Subgroup.normalizer ((K ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) := by
  exact normalizer_inf_normalizer_conjE haK haN

theorem exists_fixed_member (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ DSet Ω W) {a : G} (haN : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a = 1)
    {K : Subgroup G} (hK : K ∈ Ω) (hR₀K : R₀ ≤ K) (hR₁K : conjSub a R₀ ≤ K) :
    ∃ R ∈ DSet Ω W, conjSub a R = R := by
  exact exists_fixed_memberE (OmegaBase.ofHyp hp hΩ) hR₀ haN ha2 hK hR₀K hR₁K

theorem exists_member_of_D_same (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hTR : T ≤ R ⊔ W ⊔ OCW W) : ∃ K ∈ Ω, R ≤ K ∧ T ≤ K := by
  exact exists_member_of_D_sameE (OmegaHooks.ofHyp hp hq hΩ hW) hW hR hT hTR

omit [Finite G] in
theorem piG_one' (W : Subgroup G) : piG W 1 = 1 := by
  rw [piG_of_mem (Subgroup.one_mem _)]
  exact (piN W).map_one

omit [Finite G] in
theorem piG_mul_self_of {W : Subgroup G} {a : G} (haN : a ∈ Subgroup.normalizer (W : Set G))
    (ha2 : a * a = 1) : piG W a * piG W a = 1 := by
  rw [← piG_mul haN haN, ha2, piG_one']

omit [Finite G] in
theorem conjQ_val (hΩ : HypOmegaMod p f Ω) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    {q : ↥(muGroup Ω W)} {t : G} (ht : t ∈ Subgroup.normalizer (W : Set G))
    (hq : (q : NQuot (W ⊔ OCW W)) = piG W t) :
    (conjQ hΩ hg q : NQuot (W ⊔ OCW W)) = piG W (g * t * g⁻¹) := by
  rw [conjQ_apply, hq, piG_mul (Subgroup.mul_mem _ hg ht) (Subgroup.inv_mem _ hg), piG_mul hg ht,
    piG_inv hg]

omit [Finite G] in
theorem conjQ_mem_muDeltaOf (hΩ : HypOmegaMod p f Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {C : Set (Subgroup G)}
    (hC : ∀ T ∈ C, conjSub g T ∈ C) (hCD : ∀ T ∈ C, T ∈ DSet Ω W) {q : ↥(muGroup Ω W)}
    (hq : q ∈ muDeltaOf Ω W C) : conjQ hΩ hg q ∈ muDeltaOf Ω W C := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := hq
  refine ⟨conjSub g R, hC R hR, g * r * g⁻¹, conj_mem_conjSub hr, ?_, ?_⟩
  · rw [mem_normalizer_iff_of_mem hg]
    exact hrW
  · exact conjQ_val hΩ hg ((hCD R hR).2 hr) hra

omit [Finite G] in
theorem conjQ_mem_muDelta (hΩ : HypOmegaMod p f Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {q : ↥(muGroup Ω W)}
    (hq : q ∈ muDelta Ω W) : conjQ hΩ hg q ∈ muDelta Ω W :=
  conjQ_mem_muDeltaOf hΩ hg (fun _ hT => conjSub_mem_D hΩ hT hg) (fun _ hT => hT) hq

omit [Finite G] in
theorem conjQ_conjQ (hΩ : HypOmegaMod p f Ω) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hg2 : g * g = 1) (q : ↥(muGroup Ω W)) : conjQ hΩ hg (conjQ hΩ hg q) = q := by
  apply Subtype.ext
  have hpa := piG_mul_self_of hg hg2
  have hinv : (piG W g)⁻¹ = piG W g := inv_eq_of_mul_eq_one_left hpa
  rw [conjQ_apply, conjQ_apply, hinv]
  calc piG W g * (piG W g * q.1 * piG W g) * piG W g
      = (piG W g * piG W g) * q.1 * (piG W g * piG W g) := by group
    _ = q.1 := by rw [hpa, one_mul, mul_one]

theorem dComm_of_commute (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {R₁ R₂ : Subgroup G} (h₁ : R₁ ∈ DSet Ω W) (h₂ : R₂ ∈ DSet Ω W) {r₁ r₂ : G}
    (hr₁ : r₁ ∈ R₁) (hr₂ : r₂ ∈ R₂) (hr₁W : r₁ ∉ W) (hr₂W : r₂ ∉ W)
    (hcomm : piG W r₁ * piG W r₂ = piG W r₂ * piG W r₁) (hne : piG W r₁ ≠ piG W r₂) :
    DComm W R₁ R₂ := by
  exact dComm_of_commuteE (OmegaHooks.ofHyp hp hq hΩ hW) h₁ h₂ hr₁ hr₂ hr₁W hr₂W hcomm hne

theorem exists_orderOf_four (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    ∃ w ∈ R ⊓ W, orderOf w = 4 := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hinfo := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  obtain ⟨g, hg⟩ := exists_zpowers_eq_inf_W hp hq hΩ hW hR
  have hgm : g ∈ R ⊓ W := hg ▸ Subgroup.mem_zpowers g
  obtain ⟨j, hj⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup hRK.2.1 hgm.1
  have hcard : orderOf g = Nat.card ↥(R ⊓ W) := by rw [← hg, Nat.card_zpowers]
  have h4 : 4 ≤ orderOf g := by rw [hcard]; exact hinfo.2.2.2.1
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 4 ∣ orderOf g := by
    rw [hj]
    exact ⟨2 ^ (j - 2), by rw [show j = (j - 2) + 2 by omega, pow_add]; ring_nf; simp⟩
  refine ⟨g ^ (orderOf g / 4), Subgroup.pow_mem _ hgm _, ?_⟩
  exact orderOf_pow_orderOf_div (by omega) hdvd

theorem exists_fixed_member_of_muDelta_fixed (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω) {a : G}
    (haN : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a = 1)
    (hx : ∃ x ∈ muDelta Ω W, conjQ hΩ haN x = x) : ∃ R ∈ DSet Ω W, conjSub a R = R := by
  obtain ⟨x, ⟨R₀, hR₀, r₀, hr₀, hr₀W, hxr⟩, hax⟩ := hx
  have hR₁ : conjSub a R₀ ∈ DSet Ω W := conjSub_mem_D hΩ hR₀ haN
  have hr₁ : a * r₀ * a⁻¹ ∈ conjSub a R₀ := conj_mem_conjSub hr₀
  have hr₁W : a * r₀ * a⁻¹ ∉ W := fun h => hr₀W ((mem_normalizer_iff_of_mem haN r₀).mp h)
  have hpi : piG W (a * r₀ * a⁻¹) = piG W r₀ := by
    rw [← conjQ_val hΩ haN (hR₀.2 hr₀) hxr, hax, hxr]
  have hle : conjSub a R₀ ≤ R₀ ⊔ W ⊔ OCW W :=
    le_sup_of_piG_eq hr₀ hR₀.2 hR₁.2 fun y hy hyW =>
      (D_piG_eq hp hq hΩ hW hR₁ hy hr₁ hyW hr₁W).trans hpi
  obtain ⟨K, hK, hR₀K, hR₁K⟩ := exists_member_of_D_same hp hq hΩ hW hR₀ hR₁ hle
  exact exists_fixed_member hp hΩ hR₀ haN ha2 hK hR₀K hR₁K

theorem conj_mul_conj_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {a : G} (ha2 : a * a = 1) {w v : G} (hw : w ∈ W) (hv : v ∈ W)
    (hvd : v = a * w * a⁻¹) : a * (w * v) * a⁻¹ = w * v := by
  exact conj_mul_conj_eqE (OmegaHooks.ofHyp hp hq hΩ hW) ha2 hw hv hvd


end Fixed

end Thompson


end CFSG.ClassicalInvolution.Asc77
