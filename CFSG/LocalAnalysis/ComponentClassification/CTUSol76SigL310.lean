module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSep
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigWG

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

omit [Finite G] in
theorem orderOf_inv_mul_mul (m s : G) : orderOf (m⁻¹ * s * m) = orderOf s := by
  have h := (MulAut.conj m⁻¹).orderOf_eq s
  simp only [MulAut.conj_apply, inv_inv] at h
  exact h

theorem isElemAbelian_sup_zpowers_two {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    {s : G} (hs2 : orderOf s = 2) (hsE : s ∉ E) (hsc : s ∈ centralizer (E : Set G)) :
    CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers s) ∧
      Nat.card (E ⊔ zpowers s : Subgroup G) = 2 * Nat.card E := by
  have hzs : zpowers s ≤ centralizer (E : Set G) := zpowers_le.mpr hsc
  have hEz : E ≤ centralizer ((zpowers s : Subgroup G) : Set G) := le_centralizer_iff.mp hzs
  have hEc : E ≤ centralizer (E : Set G) := le_centralizer_iff_isMulCommutative.mpr hE.1
  have hzc : zpowers s ≤ centralizer ((zpowers s : Subgroup G) : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hA : E ⊔ zpowers s ≤ centralizer ((E ⊔ zpowers s : Subgroup G) : Set G) :=
    sup_le (le_centralizer_iff.mp (sup_le hEc hzs)) (le_centralizer_iff.mp (sup_le hEz hzc))
  have hs : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  refine ⟨⟨le_centralizer_iff_isMulCommutative.mp hA, fun x hx => ?_⟩, ?_⟩
  · have hx' : x ∈ (E : Set G) * (zpowers s : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left E (zpowers s)
        (hzs.trans (Subgroup.centralizer_le_normalizer (E : Set G)))]
      exact hx
    obtain ⟨a, ha, z, hz, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hcomm : Commute a (s ^ k) :=
      Commute.zpow_right (show Commute a s from (mem_centralizer_iff.mp hsc) a ha) k
    rw [hcomm.mul_pow, hE.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hs, one_zpow]
  · have hprod := AS81.card_sup_mul_card_inf_of_le_normalizer_left
      (hzs.trans (Subgroup.centralizer_le_normalizer (E : Set G)))
    have hbot : zpowers s ⊓ E = ⊥ := by
      have hdvd : Nat.card (zpowers s ⊓ E : Subgroup G) ∣ 2 := by
        rw [← hs2, ← Nat.card_zpowers]
        exact card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact card_eq_one.mp h
      · exfalso
        have heq : zpowers s ⊓ E = zpowers s :=
          eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h, Nat.card_zpowers, hs2]))
        have hmem : s ∈ zpowers s ⊓ E := by
          rw [heq]
          exact mem_zpowers s
        exact hsE (mem_inf.mp hmem).2
    rw [hbot, card_bot, mul_one, Nat.card_zpowers, hs2, sup_comm] at hprod
    exact hprod

theorem le_sup_of_mem_pumpSet (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {t : G} (htK' : t ∈ K') (ht2 : orderOf t = 2) {J : Subgroup G}
    (hJ : J ∈ pumpSet K (centralizer ({t} : Set G))) :
    J ≤ twoLayerIn (K ⊓ centralizer ({t} : Set G)) ⊔ oddCoreIn (centralizer ({t} : Set G)) := by
  obtain ⟨M, hM, hsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne htK' ht2
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp (ncard_pumpSet_eq_one hq hR1 hG hN hK hK' hne htK' ht2)
  rw [hM', Set.mem_singleton_iff] at hJ hM
  rw [hJ, ← hM]
  calc M ≤ M ⊔ oddCoreIn (twoLayerIn (centralizer ({t} : Set G))) := le_sup_left
    _ = _ := hsup.symm
    _ ≤ _ := sup_le_sup_left (oddCoreIn_le_of_le_normalizer (map_subtype_le _)
        (le_normalizer_twoLayerIn _)) _

theorem le_coreActionKernel_of_not_mem_pumpSet {C J : Subgroup G}
    (h212 : twoLayerIn (K ⊓ C) ≤ solomonKStarOf C) (hJ : IsTwoComponentIn J C)
    (hJp : J ∉ pumpSet K C) : twoLayerIn (K ⊓ C) ≤ coreActionKernel J := by
  by_contra hY
  by_cases hJs : J ∈ solomonKStar G
  · exact hJp ⟨⟨hJ, hJs⟩, hY⟩
  · apply hY
    refine h212.trans (iSup₂_le fun J' hJ' => ?_)
    exact GSThmB.B5a.le_coreActionKernel_of_ne hJ.1 hJ'.1.1 hJ.2 hJ'.1.2
      fun h => hJs (h ▸ hJ'.2)

theorem twoLayerIn_centralizer_le_of_mem_right (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E X : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) {s : G} (hsK' : s ∈ K')
    (hs2 : orderOf s = 2) (hEs : E ≤ centralizer ({s} : Set G))
    (hX : normalizer (E : Set G) ⊓ normalizer ((zpowers s : Subgroup G) : Set G) ≤ X)
    (hKX : K ≤ X) (hOX : oddCoreIn (centralizer ({s} : Set G)) ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have hsQ : s ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm hsK'
  obtain ⟨-, -, -, h212, -⟩ := pump_facts hK hsQ hs2
  have hE2 := isPGroup_of_isKleinFour hE
  have hEY := le_pump_of_isPGroup hK hsQ hs2 hE2 (le_inf hEK hEs)
  refine twoLayerIn_le_of_forall fun J hJ => ?_
  by_cases hJp : J ∈ pumpSet K (centralizer ({s} : Set G))
  · exact (le_sup_of_mem_pumpSet hq hR1 hG hN hK hK' hne hsK' hs2 hJp).trans
      (sup_le (((map_subtype_le _).trans inf_le_left).trans hKX) hOX)
  have hEJ : E ≤ coreActionKernel J :=
    hEY.trans (le_coreActionKernel_of_not_mem_pumpSet h212 hJ hJp)
  refine (inf_centralizer_sup_oddCoreIn_eq hE2 hEJ).symm.le.trans
    (sup_le (fun x hx => hX ⟨Subgroup.centralizer_le_normalizer (E : Set G) hx.2, ?_⟩)
      ((oddCoreIn_le_of_isTwoComponentIn hJ).trans hOX))
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [centralizer_zpowers_eq]
  exact hJ.1 hx.1


theorem twoLayerIn_centralizer_le_of_conj {X : Subgroup G} {g s : G} (hg : g ∈ X)
    (h : twoLayerIn (centralizer ({g⁻¹ * s * g} : Set G)) ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have h1 := map_centralizer_singleton (MulAut.conj g) (g⁻¹ * s * g)
  have h2 : (MulAut.conj g) (g⁻¹ * s * g) = s := by rw [MulAut.conj_apply]; group
  rw [h2] at h1
  have h3 := map_twoLayerIn (MulAut.conj g) (centralizer ({g⁻¹ * s * g} : Set G))
  rw [h1] at h3
  calc twoLayerIn (centralizer ({s} : Set G))
      = (twoLayerIn (centralizer ({g⁻¹ * s * g} : Set G))).map (MulAut.conj g).toMonoidHom :=
        h3.symm
    _ ≤ X.map (MulAut.conj g).toMonoidHom := map_mono h
    _ = X := mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)

theorem oddCoreIn_centralizer_le_normalizer_wGroup (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) {s : G} (hBs : B ≤ centralizer ({s} : Set G))
    (hVs : V ≤ centralizer ({s} : Set G)) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) :=
  le_normalizer_wGroup_of_odd_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hB8
    (coprime_card_oddCoreIn _) (hBs.trans (le_normalizer_oddCoreIn _))
    (hVs.trans (le_normalizer_oddCoreIn _))


theorem twoLayerIn_centralizer_le_of_mem_V (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G)) {v : G}
    (hvV : v ∈ V) (hv1 : v ≠ 1) :
    twoLayerIn (centralizer ({v} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hvV hv1
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hVc := comm_of_isKleinFour hV
  have hWv : wGroup E (zpowers v) = wGroup B V := by
    rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE hEK hEV hvV hv1]
    exact wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hBv : B ≤ centralizer ({v} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV hb)) v hvV).symm
  have hEv : E ≤ centralizer ({v} : Set G) := hEB.trans hBv
  refine twoLayerIn_centralizer_le_of_mem_right hq hR1 hG hN hK hK' hne hE hEK (hVK' hvV) hv2 hEv
    (fun g hg => ?_) hKW
    (oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
      hEB hEK hBv (fun w hw => mem_centralizer_singleton_iff.mpr (hVc w hw v hvV)))
  rw [← hWv]
  exact le_normalizer_wGroup hg.1 hg.2


omit [Finite G] in
theorem oddCoreIn_centralizer_le_of_conj {X : Subgroup G} {g s : G} (hg : g ∈ X)
    (h : oddCoreIn (centralizer ({g⁻¹ * s * g} : Set G)) ≤ X) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ X := by
  have h1 := map_centralizer_singleton (MulAut.conj g) (g⁻¹ * s * g)
  have h2 : (MulAut.conj g) (g⁻¹ * s * g) = s := by rw [MulAut.conj_apply]; group
  rw [h2] at h1
  have h3 := map_oddCoreIn (MulAut.conj g) (centralizer ({g⁻¹ * s * g} : Set G))
  rw [h1] at h3
  calc oddCoreIn (centralizer ({s} : Set G))
      = (oddCoreIn (centralizer ({g⁻¹ * s * g} : Set G))).map (MulAut.conj g).toMonoidHom :=
        h3.symm
    _ ≤ X.map (MulAut.conj g).toMonoidHom := map_mono h
    _ = X := mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)


end CFSG.ComponentClassification.Sol76.Sig
