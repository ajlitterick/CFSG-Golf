module

public import CFSG.Quasithin.Background.B3ThreeCore
public import CFSG.Quasithin.Background.B3ThreeChief
public import CFSG.Quasithin.Background.B3ThreeTop

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {V : Type*} [CommGroup V]

section Setup

variable {ρ : LG n →* MulAut V} {A B : Subgroup V}

theorem extBot_of_threeStep (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B)
    (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) :
    ExtBot n (resAct ρ B hS.invB) (A.subgroupOf B)
      (ψ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf B))) where
  sq m := Subtype.ext (by simpa using hV m.1)
  surj := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  equiv g m := by
    have h := hψ g (QuotientGroup.mk m)
    rw [secAct_mk] at h
    exact h
  ker m := by
    show ψ (QuotientGroup.mk m) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  fix g a ha := Subtype.ext (hS.trivA g a ha)

theorem commOn_eq_of_threeStep (hn5 : 5 ≤ n) (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B)
    (hindec : IsIndec ρ) : commOn ρ B = B := by
  have h := (commG_eq_of_threeStep hV hS hindec).1
  have h2 := commOn_commG (commutator_LG hn5) hV ρ
  rw [h] at h2
  exact h2

theorem mem_commG_resAct (hB : IsInv ρ B) (h : commOn ρ B = B) (b : ↥B) :
    b ∈ commG (resAct ρ B hB) := by
  have hle : commOn ρ B ≤ (commG (resAct ρ B hB)).map B.subtype := by
    refine commOn_le (fun g m hm => ?_)
    refine ⟨resAct ρ B hB g (⟨m, hm⟩ : ↥B) * (⟨m, hm⟩ : ↥B)⁻¹,
      mul_inv_mem_commG g (⟨m, hm⟩ : ↥B), ?_⟩
    rfl
  have hb : (b : V) ∈ commOn ρ B := by
    rw [h]
    exact b.2
  obtain ⟨b', hb', hbb⟩ := hle hb
  have : b' = b := Subtype.ext hbb
  rw [this] at hb'
  exact hb'

theorem card_subgroupOf_of_le (hle : A ≤ B) : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem eq_bot_of_subgroupOf_bot (hle : A ≤ B) (h : A.subgroupOf B = ⊥) : A = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have : (⟨a, hle ha⟩ : ↥B) ∈ A.subgroupOf B := ha
  rw [h, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)


theorem subgroupOf_le_commG (hn5 : 5 ≤ n) (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B)
    (hindec : IsIndec ρ) : A.subgroupOf B ≤ commG (resAct ρ B hS.invB) := fun a _ =>
  mem_commG_resAct hS.invB (commOn_eq_of_threeStep hn5 hV hS hindec) a

theorem A_bot_of_odd [Finite V] (hn : n = 5 ∨ n = 7) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) : A = ⊥ := by
  have hn5 : 5 ≤ n := by omega
  exact eq_bot_of_subgroupOf_bot hS.le (eq_bot_of_zeroClass hn5 (extBot_of_threeStep hV hS ψ hψ)
    (subgroupOf_le_commG hn5 hV hS hindec) (H1_natural_odd hn))

theorem A_card_of_even [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) :
    A = ⊥ ∨ Nat.card ↥A = 2 := by
  have hn5 : 5 ≤ n := by omega
  have hle := card_le_two_of_twoClass hn5 (extBot_of_threeStep hV hS ψ hψ)
    (subgroupOf_le_commG hn5 hV hS hindec) (H1_natural_even hn)
  rw [card_subgroupOf_of_le hS.le] at hle
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  by_cases h1 : Nat.card ↥A = 1
  · exact Or.inl (Subgroup.eq_bot_of_card_eq A h1)
  · right
    omega

theorem exists_iso_of_bot (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) (hA : A = ⊥) :
    ∃ φ : ↥B ≃* WV n, IsModIso (resAct ρ B hS.invB) (actL n Mod.ut0) φ := by
  have E := extBot_of_threeStep hV hS ψ hψ
  have hinj : Function.Injective (ψ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf B))) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : m ∈ A.subgroupOf B := (E.ker m).1 hm
    have h2 : (m : V) ∈ A := h1
    rw [hA, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, E.surj⟩, fun g m => E.equiv g m⟩

theorem exists_iso_of_eq_top {W : Type*} [CommGroup W] {ρW : LG n →* MulAut W} (hB : IsInv ρ B)
    (h : B = ⊤) (φ : ↥B ≃* W) (hφ : IsModIso (resAct ρ B hB) ρW φ) :
    ∃ Φ : V ≃* W, IsModIso ρ ρW Φ := by
  let e : V ≃* ↥B := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)
  refine ⟨e.trans φ, fun g v => ?_⟩
  show φ (e (ρ g v)) = ρW g (φ (e v))
  have : e (ρ g v) = resAct ρ B hB g (e v) := Subtype.ext rfl
  rw [this, hφ g (e v)]

theorem top_dichotomy {X : Type*} [CommGroup X] {ρX : LG n →* MulAut X} {d₀ : LG n → X}
    (hX2 : ∀ x : X, x ^ 2 = 1) (ht : TwoClass ρX d₀) (hfixB : fixG ρ ≤ B)
    (hM : ∀ g v, ρ g v * v⁻¹ ∈ B) (φ : ↥B ≃* X)
    (hφ : IsModIso (resAct ρ B (isInv_of_trivQ hM)) ρX φ) :
    B = ⊤ ∨ ∃ s : V, s ∉ B ∧ B ⊔ Subgroup.zpowers s = ⊤ ∧
      ∀ x, ρ x s * s⁻¹ = ((φ.symm (d₀ x) : ↥B) : V) := by
  rcases top_classify_two hX2 ht hM φ hφ with h | ⟨s, hs, hcoc, hVs⟩
  · left
    rwa [sup_eq_left.2 hfixB] at h
  · right
    rw [sup_eq_left.2 hfixB] at hs hVs
    exact ⟨s, hs, hVs, hcoc⟩

theorem classify_even_aux [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) :
    (A = ⊥ ∧ ((B = ⊤ ∧ ∃ Φ : V ≃* WV n, IsModIso ρ (actL n Mod.ut0) Φ) ∨
        (B ≠ ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ))) ∨
    (Nat.card ↥A = 2 ∧ ((B = ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
        (B ≠ ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ))) := by
  have hn5 : 5 ≤ n := by omega
  have hfix : fixG ρ = A := (commG_eq_of_threeStep hV hS hindec).2
  have hfixB : fixG ρ ≤ B := hfix ▸ hS.le
  rcases A_card_of_even hn hV hS hindec ψ hψ with hA | hA2
  · left
    refine ⟨hA, ?_⟩
    obtain ⟨φ, hφ⟩ := exists_iso_of_bot hV hS ψ hψ hA
    rcases top_dichotomy (V_sq' Mod.ut0) (H1_natural_even hn) hfixB hS.trivQ φ hφ with
      h | ⟨s, hs, hVs, hcoc⟩
    · exact Or.inl ⟨h, exists_iso_of_eq_top hS.invB h φ hφ⟩
    · refine Or.inr ⟨fun h => hs (h ▸ Subgroup.mem_top s), ?_⟩
      exact exists_iso_top_ut hn hV hS.trivQ φ hφ hs hVs hcoc
  · right
    refine ⟨hA2, ?_⟩
    obtain ⟨φ, hφ⟩ := exists_iso_core hn5 hn (extBot_of_threeStep hV hS ψ hψ)
      (subgroupOf_le_commG hn5 hV hS hindec) (by rw [card_subgroupOf_of_le hS.le]; exact hA2)
    rcases top_dichotomy (V_sq' Mod.u0) (H1_core_even hn) hfixB hS.trivQ φ hφ with
      h | ⟨s, hs, hVs, hcoc⟩
    · exact Or.inl ⟨h, exists_iso_of_eq_top hS.invB h φ hφ⟩
    · refine Or.inr ⟨fun h => hs (h ▸ Subgroup.mem_top s), ?_⟩
      exact exists_iso_top_u hn hV hS.trivQ φ hφ hs hVs hcoc

end Setup

variable {ρ : LG n →* MulAut V}

theorem classify_odd [Finite V] (hn : n = 5 ∨ n = 7) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ) :
    fixG ρ = ⊥ ∧ commG ρ = ⊤ ∧ ∃ Φ : V ≃* WV n, IsModIso ρ (actL n Mod.ut0) Φ := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨A, B, hA, hB, hS, ψ, hψ⟩ := threeStep_of_chief hn5 hone
  have hc := commG_eq_of_threeStep hV hS hindec
  have hAbot : A = ⊥ := A_bot_of_odd hn hV hS hindec ψ hψ
  obtain ⟨φ, hφ⟩ := exists_iso_of_bot hV hS ψ hψ hAbot
  have hBtop : B = ⊤ := by
    rw [eq_top_iff]
    intro s _
    obtain ⟨m, hm⟩ := exists_corr_zero (H1_natural_odd hn) hS.trivQ φ hφ s
    rw [hc.2, hAbot, Subgroup.mem_bot] at hm
    have : s = (m : V) := by
      have := mul_inv_eq_one.1 hm
      exact this
    rw [this]
    exact m.2
  exact ⟨hc.2.trans hAbot, hc.1.trans hBtop, exists_iso_of_eq_top hS.invB hBtop φ hφ⟩


theorem hasOneChief_natural (hn : 5 ≤ n) : HasOneChief n (actL n Mod.ut0) := by
  have hirr : ∀ Z : Subgroup (WV n), IsInv (actL n Mod.ut0) Z → Z = ⊥ ∨ Z = ⊤ := fun Z hZ =>
    (B3_1_1 hn).2 Z (fun g hg v hv => hZ ⟨g, hg⟩ v hv)
  have hnt : Nontrivial (WV n) := (B3_1_1 hn).1
  let ψ₀ : Sec (⊤ : Subgroup (WV n)) (⊥ : Subgroup (WV n)) ≃* WV n :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := (⊤ : Subgroup (WV n))))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  refine ⟨⟨1, fun i => if i = 0 then ⊥ else ⊤, ?_, 0, Nat.one_pos, by simp, by simp, ?_, ?_,
    ψ₀, ?_⟩⟩
  · intro i _
    by_cases h : i = 0
    · simp only [h, ite_true]
      intro g w hw
      rw [Subgroup.mem_bot] at hw ⊢
      rw [hw, map_one]
    · simp only [h, ite_false]
      intro _ _ _
      exact Subgroup.mem_top _
  · intro i hi
    have h0 : i = 0 := by omega
    subst h0
    refine ⟨bot_lt_top, fun Z hZ _ _ => hirr Z hZ⟩
  · intro i hi hne
    exact absurd (by omega) hne
  · intro g x
    induction x using QuotientGroup.induction_on with
    | H w => rfl

theorem isIndec_natural (hn : 5 ≤ n) : IsIndec (actL n Mod.ut0) := by
  intro X Y hX hY hXY _
  rcases (B3_1_1 hn).2 X (fun g hg v hv => hX ⟨g, hg⟩ v hv) with h | h
  · exact Or.inl h
  · right
    rw [h, top_inf_eq] at hXY
    exact hXY

end CFSG.Quasithin.B3
