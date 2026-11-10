module

public import CFSG.Quasithin.EmptyFaithful.S146S3
public import CFSG.Quasithin.EmptyFaithful.S146Six
public import CFSG.Quasithin.EmptyFaithful.S146Final

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Setting146

theorem isSylowTwoOf_top (S : Setting146 G T M) : IsSylowTwoOf T ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.hyp.sylow
  have := isSylowTwoOf_of_sylow P (le_top : (P : Subgroup G) ≤ ⊤)
  rwa [hP] at this

theorem isSylowTwoOf_mcOf (S : Setting146 G T M) : IsSylowTwoOf T (mcOf T) :=
  isSylowTwoOf_of_le_of_le' S.isSylowTwoOf_top (le_centralizer_quasithinOmegaOneCenter T) le_top

theorem pCoreOf_mcOf_le (S : Setting146 G T M) : pCoreOf 2 (mcOf T) ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf S.isSylowTwoOf_mcOf

theorem not_yOfL22_le_mcOf (S : Setting146 G T M) : ¬ yOfL22 T M ≤ mcOf T := by
  intro hLG
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  obtain ⟨v, hvV, hvZ⟩ : ∃ v ∈ VZ T M, v ∉ quasithinOmegaOneCenter T := by
    by_contra hcon
    push Not at hcon
    have heq : VZ T M = quasithinOmegaOneCenter T := le_antisymm hcon hZV
    have h4 := S.hyp.rank_two
    rw [heq, S.card_Z] at h4
    omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Subgroup.one_mem _)
  obtain ⟨l, hlL, hl⟩ := S.hyp1281.exists_conj_eq (le_conjClosure _ _ hzZ) hvV hz1' hv1
  have hlC := (Subgroup.mem_centralizer_iff.mp (hLG hlL)) z hzZ
  apply hvZ
  rw [← hl]
  have : l * z * l⁻¹ = z := by rw [← hlC]; group
  rw [this]
  exact hzZ

end Setting146


omit [Finite G] in
theorem perm3_alt_comm : ∀ g h : Equiv.Perm (Fin 3), Equiv.Perm.sign g = 1 →
    Equiv.Perm.sign h = 1 → g * h = h * g := by decide

omit [Finite G] in
theorem psiOf_eq_one_of_mem_map_ker {X : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {k : G}
    (hk : k ∈ (psiOf e).ker.map X.subtype) (hkX : k ∈ X) : psiOf e ⟨k, hkX⟩ = 1 := by
  obtain ⟨y, hy, hyk⟩ := hk
  have : y = ⟨k, hkX⟩ := Subtype.ext hyk
  subst this
  exact hy

namespace Setting146

theorem isSylowTwoOf_tZero (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u : G}
    (hu : IsInvU T M H u) :
    IsSylowTwoOf (tZero T u)
      (centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u)) := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hT0T : tZero T u ≤ T := centralizerMod_le_left _ _ _
  have hTH : T ≤ H := hH.1.1
  have hT0C : tZero T u ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) :=
    fun x hx => ⟨hTH hx.1, hx.2.1, hx.2.2⟩
  obtain ⟨S', hS', hle⟩ := exists_isSylowTwoOf_ge' hT0C (hT2.to_le hT0T)
  by_cases hEq : S' = tZero T u
  · rw [← hEq]; exact hS'
  · exfalso
    have hlt : tZero T u < S' := lt_of_le_of_ne hle (Ne.symm hEq)
    obtain ⟨x, hxS, hxA, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hS'.2.1 hlt
    have hxC := hS'.1 hxS
    have hxT : x ∈ T := by
      rw [← hu.normalizer_eq]
      exact ⟨hxN, S.le_mcOf hH hxC.1⟩
    exact hxA ⟨hxT, hxC.2.1, hxC.2.2⟩

theorem nonempty_oTwoQuot_I2 (S : Setting146 G T M) {H H₂ TI : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) (hQT : tZero T u = pCoreOf 2 (mcOf T) ⊔ tU T u)
    (hT0 : tZero T u ≤ H₂)
    (hH₂C : H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u))
    (hS3 : Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3))) (hTuTI : tU T u ≤ TI) (hTIH₂ : TI ≤ H₂) :
    Nonempty (OTwoQuot (oTwoUpper H₂ ⊔ TI) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := hS3
  have hT0S : IsSylowTwoOf (tZero T u) H₂ :=
    isSylowTwoOf_of_le_of_le' (S.isSylowTwoOf_tZero hH hu) hT0 hH₂C
  have hH₂eq : H₂ ≤ oTwoUpper H₂ ⊔ tZero T u :=
    F7.isSylowTwoOf_le_sup_of_two_power hT0S (le_normalizer_oTwoUpper H₂)
      (fun x hx => exists_pow_mem_oTwoUpper H₂ hx)
  have hT0_2 : IsPGroup 2 (tZero T u) := S.hyp.sylow.1.to_le (centralizerMod_le_left _ _ _)
  have hOH₂ : oTwoUpper H₂ ≤ H₂ := oTwoUpper_le H₂
  have hYX : oTwoUpper H₂ ⊔ TI ≤ H₂ := sup_le hOH₂ hTIH₂
  obtain ⟨a, haO, haX, haψ⟩ : ∃ a ∈ oTwoUpper H₂, ∃ ha : a ∈ H₂, psiOf e ⟨a, ha⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact false_of_le_ker_sup e hOH₂ hT0 hT0_2 (fun k hk => hcon k hk (hOH₂ hk)) hH₂eq
  obtain ⟨b₀, hb₀, hb₀X, hb₀s⟩ : ∃ b ∈ tZero T u, ∃ hb : b ∈ H₂,
      Equiv.Perm.sign (psiOf e ⟨b, hb⟩) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    let K : Subgroup G := ((Equiv.Perm.sign.comp (psiOf e)).ker).map H₂.subtype
    have hOK : oTwoUpper H₂ ≤ K := fun x hx => ⟨⟨x, hOH₂ hx⟩, by
      show Equiv.Perm.sign (psiOf e ⟨x, hOH₂ hx⟩) = 1
      exact sign_psiOf_eq_one_of_oTwoUpper e hOH₂ (oTwoUpper_oTwoUpper H₂) hx, rfl⟩
    have hTK : tZero T u ≤ K := fun x hx => ⟨⟨x, hT0 hx⟩, hcon x hx (hT0 hx), rfl⟩
    have hH₂K : H₂ ≤ K := hH₂eq.trans (sup_le hOK hTK)
    obtain ⟨x, hx⟩ := psiOf_surjective e (Equiv.swap 0 1)
    obtain ⟨y, hy, hyx⟩ := hH₂K x.2
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    have h1 : Equiv.Perm.sign (psiOf e y) = 1 := hy
    rw [hx] at h1
    revert h1
    decide
  have hTuN : tU T u ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
    (inf_le_left.trans (le_centralizer_quasithinOmegaOneCenter T)).trans
      (le_normalizer_pCoreOf 2 (mcOf T))
  have hb₀' : b₀ ∈ ((tU T u ⊔ pCoreOf 2 (mcOf T) : Subgroup G) : Set G) := by
    rw [sup_comm, ← hQT]; exact hb₀
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTuN] at hb₀'
  obtain ⟨t, ht, q, hq, hb⟩ := hb₀'
  have hQ₁T0 : pCoreOf 2 (mcOf T) ≤ tZero T u := by rw [hQT]; exact le_sup_left
  have hQ₁H₂ : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 H₂ := by
    refine le_pCoreOf_of_le_normalizer 2 (hQ₁T0.trans hT0) ?_ (pCoreOf_isPGroup 2 _)
    exact (hH₂C.trans (centralizerMod_le_left _ _ _)).trans
      ((S.le_mcOf hH).trans (le_normalizer_pCoreOf 2 (mcOf T)))
  have htH₂ : t ∈ H₂ := hT0 (tU_le_tZero T u ht)
  have hqH₂ : q ∈ H₂ := pCoreOf_le 2 H₂ (hQ₁H₂ hq)
  have hψq : psiOf e ⟨q, hqH₂⟩ = 1 := (psiOf_eq_one_iff e _).mpr (hQ₁H₂ hq)
  have hψb : psiOf e ⟨b₀, hb₀X⟩ = psiOf e ⟨t, htH₂⟩ := by
    have : (⟨b₀, hb₀X⟩ : ↥H₂) = ⟨t, htH₂⟩ * ⟨q, hqH₂⟩ := Subtype.ext hb.symm
    rw [this, map_mul, hψq, mul_one]
  have haY : a ∈ oTwoUpper H₂ ⊔ TI := Subgroup.mem_sup_left haO
  have htY : t ∈ oTwoUpper H₂ ⊔ TI := Subgroup.mem_sup_right (hTuTI ht)
  refine nonempty_oTwoQuot_of_exists e hYX haY htY
    (sign_psiOf_eq_one_of_oTwoUpper e hOH₂ (oTwoUpper_oTwoUpper H₂) haO) haψ ?_
  rw [← hψb]
  exact hb₀s

theorem nonempty_oTwoQuot_I1 (S : Setting146 G T M) {I TI : Subgroup G} {u : G}
    (hL : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M))
    (hL3 : yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆)
    (hC : pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G) ≤ TI) (hTIT : TI ≤ T) :
    Nonempty (OTwoQuot (lI T M I ⊔ TI) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := S.facts.sThree
  have hLX : yOfL22 T M ≤ yOfL22 T M ⊔ T := le_sup_left
  have hTX : T ≤ yOfL22 T M ⊔ T := le_sup_right
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hlIL : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  have hlIX : lI T M I ≤ yOfL22 T M ⊔ T := hlIL.trans hLX
  have hXN : yOfL22 T M ⊔ T ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
    sup_le Subgroup.le_normalizer (S.hyp.m_max.1.2.trans S.hyp1281.normal)
  let Kker : Subgroup G := ((psiOf e).ker).map (yOfL22 T M ⊔ T).subtype
  have hO2L : pCoreOf 2 (yOfL22 T M) ≤ Kker := fun x hx =>
    ⟨⟨x, hLX (pCoreOf_le 2 _ hx)⟩, (psiOf_eq_one_iff e _).mpr
      (F7.pCoreOf_mono_of_le_normalizer hLX hXN hx), rfl⟩
  have hLK_false : yOfL22 T M ≤ Kker → False := fun hLK =>
    false_of_le_ker_sup e hLX hTX hT2
      (fun k hk => psiOf_eq_one_of_mem_map_ker e (hLK hk) (hLX hk)) le_rfl
  obtain ⟨a, haA, haX, haψ⟩ : ∃ a ∈ lI T M I, ∃ ha : a ∈ yOfL22 T M ⊔ T, psiOf e ⟨a, ha⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hlIK : lI T M I ≤ Kker := fun x hx => ⟨⟨x, hlIX hx⟩, hcon x hx (hlIX hx), rfl⟩
    exact hLK_false (hL.le.trans (sup_le hlIK hO2L))
  obtain ⟨c, hcC, hcX, hcs⟩ : ∃ c ∈ pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G),
      ∃ hc : c ∈ yOfL22 T M ⊔ T, Equiv.Perm.sign (psiOf e ⟨c, hc⟩) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hLK_false
    refine hL3.le.trans ?_
    rw [Subgroup.commutator_le]
    intro l hl c hc
    have hlX := hLX hl
    have hcX : c ∈ yOfL22 T M ⊔ T := hTX (S.pCoreOf_mcOf_le hc.1)
    have h1 : Equiv.Perm.sign (psiOf e ⟨l, hlX⟩) = 1 :=
      sign_psiOf_eq_one_of_oTwoUpper e hLX S.hyp1281.residual hl
    have h2 : Equiv.Perm.sign (psiOf e ⟨c, hcX⟩) = 1 := hcon c hc hcX
    have hcomm := perm3_alt_comm _ _ h1 h2
    refine ⟨⟨⁅l, c⁆, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlX hcX)
      (Subgroup.inv_mem _ hlX)) (Subgroup.inv_mem _ hcX)⟩, ?_, rfl⟩
    show psiOf e ⟨l * c * l⁻¹ * c⁻¹, _⟩ = 1
    have : (⟨l * c * l⁻¹ * c⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlX hcX)
      (Subgroup.inv_mem _ hlX)) (Subgroup.inv_mem _ hcX)⟩ : ↥(yOfL22 T M ⊔ T)) =
        ⟨l, hlX⟩ * ⟨c, hcX⟩ * ⟨l, hlX⟩⁻¹ * ⟨c, hcX⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hYX : lI T M I ⊔ TI ≤ yOfL22 T M ⊔ T := sup_le hlIX (hTIT.trans hTX)
  exact nonempty_oTwoQuot_of_exists e hYX (Subgroup.mem_sup_left haA)
    (Subgroup.mem_sup_right (hC hcC))
    (sign_psiOf_eq_one_of_oTwoUpper e hlIX (oTwoUpper_oTwoUpper _) haA) haψ hcs

end Setting146


end CFSG.Quasithin
