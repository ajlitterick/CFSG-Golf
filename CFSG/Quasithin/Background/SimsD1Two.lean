module

public import CFSG.Quasithin.Background.D15Three
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.Quasithin.SimsD1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F D15Proof
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem isMaxElemAbelian_iff_of_thompsonJ_le {S R : Subgroup G} (hJ : thompsonJ S ≤ R)
    (hRS : R ≤ S) (A : Subgroup G) : IsMaxElemAbelian R A ↔ IsMaxElemAbelian S A := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
  have hle : ∀ {B : Subgroup G}, IsMaxElemAbelian S B → B ≤ thompsonJ S := fun hB =>
    le_iSup₂_of_le _ hB le_rfl
  constructor
  · intro hA
    refine ⟨hA.1.trans hRS, hA.2.1, fun C hCS hC => ?_⟩
    exact (hA₀.2.2 C hCS hC).trans (hA.2.2 A₀ ((hle hA₀).trans hJ) hA₀.2.1)
  · intro hA
    exact ⟨(hle hA).trans hJ, hA.2.1, fun B hBR hB => hA.2.2 B (hBR.trans hRS) hB⟩


section Lemma34

variable {G₁ G₂ T V M₂ : Subgroup G}


end Lemma34

theorem inf_centralizer_le_of_isMaxElemAbelian {T U A : Subgroup G} (hU : IsElemAbelian 2 U)
    (hUT : U ≤ T) (hA : IsMaxElemAbelian T A) : U ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
  have hce : IsElemAbelian 2 (U ⊓ Subgroup.centralizer (A : Set G)) :=
    isElemAbelian_mono inf_le_left hU
  have hE : IsElemAbelian 2 (A ⊔ (U ⊓ Subgroup.centralizer (A : Set G))) :=
    isElemAbelian_sup_of_commute hA.2.1 hce fun a ha c hc =>
      Subgroup.mem_centralizer_iff.mp hc.2 a ha
  have hET : A ⊔ (U ⊓ Subgroup.centralizer (A : Set G)) ≤ T := sup_le hA.1 (inf_le_left.trans hUT)
  have h := Subgroup.eq_of_le_of_card_ge
    (le_sup_left : A ≤ A ⊔ (U ⊓ Subgroup.centralizer (A : Set G))) (hA.2.2 _ hET hE)
  exact le_sup_right.trans (le_of_eq h.symm)

theorem sup_centralizer_card {T U A D : Subgroup G} (hU : IsElemAbelian 2 U) (hUT : U ≤ T)
    (hA : IsMaxElemAbelian T A) (hDA : D ≤ A)
    (hCD : A ⊓ Subgroup.centralizer (U : Set G) ≤ D) :
    IsElemAbelian 2 (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G))) ∧
      D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)) ≤ T ∧
      Nat.card (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)) : Subgroup G) *
          Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
        (D ⊓ Subgroup.centralizer (U : Set G)).relIndex D *
          Nat.card (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) *
          Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
  have hUA := inf_centralizer_le_of_isMaxElemAbelian hU hUT hA
  have hDe : IsElemAbelian 2 D := isElemAbelian_mono hDA hA.2.1
  have hcomm : ∀ d ∈ D, ∀ c ∈ U ⊓ Subgroup.centralizer (D : Set G), d * c = c * d :=
    fun d hd c hc => Subgroup.mem_centralizer_iff.mp hc.2 d hd
  have hCe : IsElemAbelian 2 (U ⊓ Subgroup.centralizer (D : Set G)) :=
    isElemAbelian_mono inf_le_left hU
  refine ⟨isElemAbelian_sup_of_commute hDe hCe hcomm,
    sup_le (hDA.trans hA.1) (inf_le_left.trans hUT), ?_⟩
  have hDC : D ⊓ (U ⊓ Subgroup.centralizer (D : Set G)) =
      U ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · rintro x ⟨hxD, hxU, -⟩
      exact ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun a ha =>
        isElemAbelian_comm hA.2.1 ha (hDA hxD)⟩
    · rintro x ⟨hxU, hxC⟩
      have hxA : x ∈ A := hUA ⟨hxU, hxC⟩
      have hxUc : x ∈ Subgroup.centralizer (U : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun u hu => isElemAbelian_comm hU hu hxU
      exact ⟨hCD ⟨hxA, hxUc⟩, hxU, Subgroup.centralizer_le (fun y hy => hDA hy) hxC⟩
  have hDU : D ⊓ Subgroup.centralizer (U : Set G) = A ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (inf_le_inf_right _ hDA) (le_inf hCD inf_le_right)
  have h1 := card_sup_mul_card_inf_of_commute hcomm
  have h2 := Subgroup.relIndex_mul_card (D ⊓ Subgroup.centralizer (U : Set G)) D
  rw [inf_eq_left.mpr inf_le_left] at h2
  rw [hDC] at h1
  calc _ = Nat.card D * Nat.card (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) := h1
    _ = _ := by rw [← h2, hDU]; ring

theorem offender_value_le {T U A D : Subgroup G} (hU : IsElemAbelian 2 U) (hUT : U ≤ T)
    (hA : IsMaxElemAbelian T A) (hDA : D ≤ A)
    (hCD : A ⊓ Subgroup.centralizer (U : Set G) ≤ D) :
    (D ⊓ Subgroup.centralizer (U : Set G)).relIndex D *
        Nat.card (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) ≤
      (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ∧
    ((D ⊓ Subgroup.centralizer (U : Set G)).relIndex D *
        Nat.card (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) =
      (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) →
      IsMaxElemAbelian T (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)))) := by
  obtain ⟨hse, hsT, hD⟩ := sup_centralizer_card hU hUT hA hDA hCD
  obtain ⟨-, -, hA'⟩ := sup_centralizer_card hU hUT hA (le_refl A) inf_le_left
  rw [sup_eq_left.mpr (inf_centralizer_le_of_isMaxElemAbelian hU hUT hA)] at hA'
  have hle : Nat.card (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)) : Subgroup G) ≤ Nat.card A :=
    hA.2.2 _ hsT hse
  have hc : 0 < Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hk : 0 < Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := Nat.card_pos
  refine ⟨Nat.le_of_mul_le_mul_right ?_ hk, fun heq => ?_⟩
  · calc _ = Nat.card (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)) : Subgroup G) *
          Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hD.symm
      _ ≤ Nat.card A * Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hle
      _ = _ := hA'
  · have hs : Nat.card (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)) : Subgroup G) =
        Nat.card A := by
      refine Nat.eq_of_mul_eq_mul_right hc ?_
      rw [hD, hA', heq]
    exact ⟨hsT, hse, fun B hBT hB => (hA.2.2 B hBT hB).trans hs.ge⟩

omit [Finite G] in
theorem exists_lift_autOn {U A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (U : Set G))
    {F : Subgroup (MulAut U)} (hF : F ≤ autOn A U) :
    ∃ D : Subgroup G, D ≤ A ∧ A ⊓ Subgroup.centralizer (U : Set G) ≤ D ∧ autOn D U = F := by
  refine ⟨A ⊓ (F.comap (conjAct U)).map (Subgroup.normalizer (U : Set G)).subtype, inf_le_left,
    ?_, ?_⟩
  · rintro x ⟨hxA, hxC⟩
    refine ⟨hxA, ⟨x, hAN hxA⟩, ?_, rfl⟩
    show conjAct U ⟨x, hAN hxA⟩ ∈ F
    rw [(EmptyFaithfulMultiple.conjAct_eq_one_iff ⟨x, hAN hxA⟩).mpr hxC]
    exact F.one_mem
  · apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      have hn' : (n : G) ∈
          A ⊓ (F.comap (conjAct U)).map (Subgroup.normalizer (U : Set G)).subtype := hn
      obtain ⟨m, hm, hmn⟩ := hn'.2
      have hmn' : m = n := Subtype.ext hmn
      rw [← hmn']
      exact hm
    · intro b hb
      obtain ⟨n, hn, rfl⟩ := hF hb
      exact ⟨n, ⟨hn, n, hb, rfl⟩, rfl⟩

omit [Finite G] in
theorem commutator_commutator_eq_bot_of_isQuadratic {U A : Subgroup G} (hU : IsElemAbelian 2 U)
    (hAN : A ≤ Subgroup.normalizer (U : Set G))
    (hq : @IsQuadratic ↥U (commGroupOfElemAbelian hU) (autOn A U)) : ⁅⁅U, A⁆, A⁆ = ⊥ := by
  let _ : CommGroup U := commGroupOfElemAbelian hU
  have hcoe : ∀ (g : Subgroup.normalizer (U : Set G)) (v : U),
      ((conjAct U g v : U) : G) = g * v * (g : G)⁻¹ := fun g v => AutOn.coe_conjAct_apply U g v
  have key : ∀ u ∈ U, ∀ a ∈ A, ⁅u, a⁆ ∈ U ⊓ Subgroup.centralizer (A : Set G) := by
    intro u hu a ha
    have h1 : a * u⁻¹ * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (U.inv_mem hu)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def, show u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) by group]
      exact U.mul_mem hu h1
    rw [Subgroup.mem_centralizer_iff]
    intro a' ha'
    have hw : (conjAct U ⟨a, hAN ha⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : U)⁻¹ : U) ∈ commV (autOn A U) :=
      Subgroup.subset_closure ⟨_, AutOn.conjAct_mem_autOn_of_mem (hAN ha) ha, ⟨u, hu⟩, rfl⟩
    have hfix := hq hw _ (AutOn.conjAct_mem_autOn_of_mem (hAN ha') ha')
    have h2 := congrArg (fun z : U => (z : G)) hfix
    simp only [hcoe, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have hc : a' * (a * u * a⁻¹ * u⁻¹) = (a * u * a⁻¹ * u⁻¹) * a' := by
      calc a' * (a * u * a⁻¹ * u⁻¹)
          = a' * (a * u * a⁻¹ * u⁻¹) * a'⁻¹ * a' := by group
        _ = (a * u * a⁻¹ * u⁻¹) * a' := by rw [h2]
    have hc' : a' * (a * u * a⁻¹ * u⁻¹)⁻¹ = (a * u * a⁻¹ * u⁻¹)⁻¹ * a' :=
      (Commute.inv_right (show Commute a' (a * u * a⁻¹ * u⁻¹) from hc)).eq
    rw [commutatorElement_def]
    calc a' * (u * a * u⁻¹ * a⁻¹) = a' * (a * u * a⁻¹ * u⁻¹)⁻¹ := by group
      _ = (a * u * a⁻¹ * u⁻¹)⁻¹ * a' := hc'
      _ = u * a * u⁻¹ * a⁻¹ * a' := by group
  have hle : ⁅U, A⁆ ≤ U ⊓ Subgroup.centralizer (A : Set G) := Subgroup.commutator_le.mpr key
  refine le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans (le_of_eq ?_))
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact inf_le_right

theorem exists_quadratic_replacement {T U A : Subgroup G} (hU : IsElemAbelian 2 U) (hUT : U ≤ T)
    (hAN : A ≤ Subgroup.normalizer (U : Set G)) (hA : IsMaxElemAbelian T A)
    (hnc : ¬ A ≤ Subgroup.centralizer (U : Set G)) :
    ∃ A' : Subgroup G, IsMaxElemAbelian T A' ∧ A' ≤ A ⊔ U ∧ ⁅⁅U, A'⁆, A'⁆ = ⊥ ∧
      ¬ A' ≤ Subgroup.centralizer (U : Set G) := by
  let _ : CommGroup U := commGroupOfElemAbelian hU
  have hsq : ∀ v : U, v ^ 2 = 1 := fun v => Subtype.ext (hU.2 v v.2)
  have hXne : autOn A U ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hAN hnc
  have hXel : IsElemAbelian2 (autOn A U) := isElemAbelian2_autOn hU hA.2.1 hAN
  have hXo : IsFFStarOffender (autOn A U) (autOn A U) := by
    refine ⟨le_rfl, hXne, hXel, fun B hB => ?_⟩
    obtain ⟨D, hDA, hCD, rfl⟩ := exists_lift_autOn hAN hB
    have hDN : D ≤ Subgroup.normalizer (U : Set G) := hDA.trans hAN
    rw [card_autOn_eq_relIndex hDN, card_fixV_autOn_eq hU hDN, card_autOn_eq_relIndex hAN,
      card_fixV_autOn_eq hU hAN]
    exact (offender_value_le hU hUT hA hDA hCD).1
  obtain ⟨F, hFX, hFo, hFq, hFc, -⟩ := exists_quadratic_offender_le hsq hXo
  obtain ⟨D, hDA, hCD, rfl⟩ := exists_lift_autOn hAN hFX
  have hDN : D ≤ Subgroup.normalizer (U : Set G) := hDA.trans hAN
  rw [card_autOn_eq_relIndex hDN, card_fixV_autOn_eq hU hDN, card_autOn_eq_relIndex hAN,
    card_fixV_autOn_eq hU hAN] at hFc
  have hmax := (offender_value_le hU hUT hA hDA hCD).2 hFc
  have hCN : U ⊓ Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    fun x hx => Subgroup.le_normalizer hx.1
  have hUU : U ≤ Subgroup.centralizer (U : Set G) := le_centralizer_self hU
  have hC0 : autOn (U ⊓ Subgroup.centralizer (D : Set G)) U = ⊥ :=
    AutOn.autOn_eq_bot_of_le_centralizer (inf_le_left.trans hUU)
  have hA'N : D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)) ≤ Subgroup.normalizer (U : Set G) :=
    sup_le hDN hCN
  have hAut : autOn (D ⊔ (U ⊓ Subgroup.centralizer (D : Set G))) U = autOn D U := by
    rw [AutOn.autOn_sup_eq hDN hCN, hC0, sup_bot_eq]
  refine ⟨D ⊔ (U ⊓ Subgroup.centralizer (D : Set G)), hmax,
    sup_le (hDA.trans le_sup_left) (inf_le_left.trans le_sup_right), ?_, ?_⟩
  · refine commutator_commutator_eq_bot_of_isQuadratic hU hA'N ?_
    rw [hAut]
    exact hFq
  · intro hle
    exact hFo.2.1 (AutOn.autOn_eq_bot_of_le_centralizer (le_sup_left.trans hle))

section Main


end Main

end CFSG.Quasithin.SimsD1
