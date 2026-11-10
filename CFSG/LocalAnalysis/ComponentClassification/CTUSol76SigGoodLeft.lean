module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGoodRight

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

omit [Finite G] in
theorem sigPair_of_le_centralizer_right {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    {U : Subgroup G} (hU : IsKleinFour U) (hUY : U ≤ K' ⊓ centralizer (B : Set G)) :
    SigPair N K K' U B := by
  obtain ⟨hK, hK', hne, -, -, hBQ, -, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  refine ⟨hK, hK', hne, hU, hUY.trans inf_le_left, hBQ, fun b hb => mem_centralizer_iff.mpr
    fun u hu => ((mem_centralizer_iff.mp (hUY hu).2) b hb).symm, hB, hB8, hBN, E, hE, hEB, hEK⟩

theorem wGroup_eq_of_le_centralizer_right' (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {U : Subgroup G} (hU : IsKleinFour U)
    (hUY : U ≤ K' ⊓ centralizer (B : Set G)) : wGroup B U = wGroup B V := by
  have hPU := sigPair_of_le_centralizer_right hP hU hUY
  obtain ⟨hK, hK', hne, -, hUK', hBQ, hBU, hB, -, -, E, hE, hEB, hEK⟩ := hPU
  exact (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hU hUK' hBQ hBU hB hE hEB hEK hE
    hEB).symm.trans (wGroup_eq_of_le_centralizer_right hq hR1 hG hN hP hK'W hE hEB hEK hU hUY)

theorem isGoodFor_of_reflTransGen_left (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    {E : Subgroup G} (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K) {F : Subgroup G}
    (hEF : Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) {x : G}
    (hxF : x ∈ F) (hx1 : x ≠ 1) : IsGoodFor N (wGroup B V) x := by
  classical
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, -, -, -⟩ := hP'
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hKQ : K ≤ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK (Ne.symm hne)
  induction hEF generalizing x with
  | refl => exact ⟨hx1, K, K', V, B, hP, rfl, Or.inl (hEB hxF)⟩
  | @tail C D hEC hCD ih =>
    by_cases hCD' : C = D
    · subst hCD'
      exact ih hxF hx1
    have hWD : wGroup D V = wGroup B V :=
      (wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hEC.tail hCD)).trans hWE
    obtain ⟨hC, hD, hCX, hDX, hCDc⟩ := hCD
    have hCD'' : ¬ C ≤ D := fun hle => hCD' (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hC.card_four, hD.card_four]))
    obtain ⟨c, hcC, hcD⟩ := IsConcreteLE.not_le_iff_exists.mp hCD''
    have hc1 : c ≠ 1 := fun h => hcD (h ▸ D.one_mem)
    have hc2 : orderOf c = 2 := orderOf_eq_two_of_isKleinFour hC hcC hc1
    have hDK : D ≤ K := hDX.trans inf_le_left
    have hcK : c ∈ K := (hCX hcC).1
    obtain ⟨hAe, hA8⟩ := isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hD) hc2 hcD
      (hCDc hcC)
    have hAQ : D ⊔ zpowers c ≤ coreActionKernel K' :=
      sup_le (hDK.trans hKQ) (zpowers_le.mpr (hKQ hcK))
    have hAV : D ⊔ zpowers c ≤ centralizer (V : Set G) :=
      sup_le (hDX.trans inf_le_right) (zpowers_le.mpr (hCX hcC).2)
    have hAN : D ⊔ zpowers c ≤ N := sup_le (hDK.trans hK.1.1) (zpowers_le.mpr (hK.1.1 hcK))
    have hPA : SigPair N K K' V (D ⊔ zpowers c) := ⟨hK, hK', hne, hV, hVK', hAQ, hAV, hAe,
      by rw [hA8, hD.card_four], hAN, D, hD, le_sup_left, hDK⟩
    have hWA : wGroup (D ⊔ zpowers c) V = wGroup D V :=
      (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hAe hD le_sup_left hDK hD
        le_sup_left).symm
    exact ⟨hx1, K, K', V, D ⊔ zpowers c, hPA, hWA.trans hWD, Or.inl (mem_sup_left hxF)⟩


end CFSG.ComponentClassification.Sol76.Sig
