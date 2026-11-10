module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigComp

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem wGroup_zpowers_eq_of_commute (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) {t t' : G}
    (ht : t ∈ K' ⊓ centralizer (E : Set G)) (ht' : t' ∈ K' ⊓ centralizer (E : Set G))
    (ht2 : orderOf t = 2) (ht'2 : orderOf t' = 2) (htt' : t ≠ t') (hcomm : t * t' = t' * t) :
    wGroup E (zpowers t) = wGroup E (zpowers t') := by
  set V' := closure ({t, t'} : Set G) with hV'
  have hV'4 : IsKleinFour V' :=
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair ht2 ht'2 hcomm htt'
  have hV'K' : V' ≤ K' := by
    rw [hV', closure_le]
    rintro x (rfl | rfl)
    · exact ht.1
    · exact ht'.1
  have hEV' : E ≤ centralizer (V' : Set G) := by
    intro e he
    rw [hV', mem_centralizer_iff]
    intro x hx
    have hxC : x ∈ centralizer (E : Set G) := by
      have hle : V' ≤ centralizer (E : Set G) := by
        rw [hV', closure_le]
        rintro y (rfl | rfl)
        · exact ht.2
        · exact ht'.2
      exact hle hx
    exact ((mem_centralizer_iff.mp hxC) e he).symm
  have htV' : t ∈ V' := subset_closure (Set.mem_insert t _)
  have ht'V' : t' ∈ V' := subset_closure (Set.mem_insert_of_mem t rfl)
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  have ht'1 : t' ≠ 1 := fun h => by rw [h, orderOf_one] at ht'2; norm_num at ht'2
  rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV'4 hV'K' hE hEK hEV' htV' ht1,
    wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV'4 hV'K' hE hEK hEV' ht'V' ht'1]

theorem wGroup_zpowers_eq_of_reachable (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K)
    {a b : {t : ↥(K' ⊓ centralizer (E : Set G)) // orderOf t = 2}}
    (h : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Reachable a b) :
    wGroup E (zpowers (((a : ↥(K' ⊓ centralizer (E : Set G))) : G))) =
      wGroup E (zpowers (((b : ↥(K' ⊓ centralizer (E : Set G))) : G))) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail c d _ hadj ih =>
    rw [ih]
    rw [CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hcd, hcomm⟩ := hadj
    have hc2 : orderOf (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact c.2
    have hd2 : orderOf (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact d.2
    have hne' : (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) ≠
        (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) :=
      fun h => hcd (Subtype.ext (Subtype.ext h))
    have hcomm' : (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) *
        (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) =
          (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) *
            (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) := by
      rcases hcomm with h | h
      · exact congrArg Subtype.val h
      · exact (congrArg Subtype.val h).symm
    exact wGroup_zpowers_eq_of_commute h32 hG hN hK hK' hne hE hEK c.1.2 d.1.2 hc2 hd2
      hne' hcomm'


@[expose] def CommFourIn (X F F' : Subgroup G) : Prop :=
  IsKleinFour F ∧ IsKleinFour F' ∧ F ≤ X ∧ F' ≤ X ∧ F ≤ centralizer (F' : Set G)

theorem wGroup_eq_of_reflTransGen (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V E F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (h : Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) :
    wGroup F V = wGroup E V := by
  induction h with
  | refl => rfl
  | @tail C D _ hCD ih =>
    rw [← ih]
    obtain ⟨hC, hD, hCX, hDX, hCDc⟩ := hCD
    have hDCc : D ≤ centralizer (C : Set G) := fun d hd => mem_centralizer_iff.mpr fun c hc =>
      ((mem_centralizer_iff.mp (hCDc hc)) d hd).symm
    exact le_antisymm
      (wGroup_le_wGroup h32 hG hN hK hK' hne hV hVK' hD (hDX.trans inf_le_left)
        (hDX.trans inf_le_right) hC (hCX.trans inf_le_left) (hCX.trans inf_le_right) hDCc)
      (wGroup_le_wGroup h32 hG hN hK hK' hne hV hVK' hC (hCX.trans inf_le_left)
        (hCX.trans inf_le_right) hD (hDX.trans inf_le_left) (hDX.trans inf_le_right) hCDc)


end CFSG.ComponentClassification.Sol76.Sig
