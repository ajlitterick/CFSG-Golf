module

public import CFSG.LocalAnalysis.SteinbergSFBothTrivialWeylProducts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace BothTrivialHeisenberg

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem eq_zero_of_comm_one {b c d : K}
    (hc : uElt 0 b c d * uElt 1 0 0 0 = uElt 1 0 0 0 * uElt 0 b c d) : d = 0 := by
  rw [uElt_mul, uElt_mul] at hc
  linear_combination -(uElt_inj hc).2.1

theorem eq_zero_of_comm_two {a b c : K}
    (hc : uElt a b c 0 * uElt 0 0 0 1 = uElt 0 0 0 1 * uElt a b c 0) : a = 0 := by
  rw [uElt_mul, uElt_mul] at hc
  linear_combination (uElt_inj hc).2.1

end Model

section Center

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐀[" i "]" => pull φ (rootA K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀" => (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)

omit [Finite G] [Finite K] in
theorem A_inf_A_swap (i : Axis) : 𝐀[i] ⊓ 𝐀[i.swap] = 𝐙 := by
  rw [← pull_inf]
  cases i
  · exact congrArg (pull φ) radA1_inf_radA2
  · exact congrArg (pull φ) ((inf_comm _ _).trans radA1_inf_radA2)

omit [Finite G] [Finite K] in
theorem mem_ZP_of_comm_A (i : Axis) {x : G} (hx : x ∈ 𝐀[i])
    (hc : ∀ y ∈ 𝐀[i.swap], x * y = y * x) : x ∈ 𝐙 := by
  obtain ⟨u, hu, rfl⟩ := exists_eq_symm_of_mem_pull hx
  cases i
  · obtain ⟨b, c, d, rfl⟩ := hu
    have h1 := hc _ (symm_mem_pull.mpr (⟨1, 0, 0, rfl⟩ : uElt (1 : K) 0 0 0 ∈ radA2 K))
    have h2 : uElt 0 b c d * uElt 1 0 0 0 = uElt 1 0 0 0 * uElt (0 : K) b c d := by
      apply φ.symm.injective
      apply Subtype.ext
      simpa only [map_mul, coe_mul] using h1
    rw [eq_zero_of_comm_one h2]
    exact symm_mem_pull.mpr ⟨b, c, rfl⟩
  · obtain ⟨a, b, c, rfl⟩ := hu
    have h1 := hc _ (symm_mem_pull.mpr (⟨0, 0, 1, rfl⟩ : uElt (0 : K) 0 0 1 ∈ radA1 K))
    have h2 : uElt a b c 0 * uElt 0 0 0 1 = uElt 0 0 0 1 * uElt a b c (0 : K) := by
      apply φ.symm.injective
      apply Subtype.ext
      simpa only [map_mul, coe_mul] using h1
    rw [eq_zero_of_comm_two h2]
    exact symm_mem_pull.mpr ⟨b, c, rfl⟩

theorem R_inf_R_swap (h : FCHyp L K n φ t) (i : Axis) : 𝐑[i] ⊓ 𝐑[i.swap] = 𝐇 := by
  cases i
  · exact R_inf_R h
  · rw [inf_comm]
    exact R_inf_R h

theorem L_inf_L_swap (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ⊓ 𝐋[i.swap] = 𝐅 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (F_le_L i) (F_le_L i.swap))
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← FullCenterWeyl.L_mul h i] at hx1
  obtain ⟨f, hf, a, ha, rfl⟩ := hx1
  have haL : a ∈ 𝐋[i.swap] := by
    have := mul_mem (inv_mem (F_le_L i.swap hf)) hx2
    rwa [inv_mul_cancel_left] at this
  have haA : a ∈ 𝐀[i.swap] :=
    (L_inf_P h i.swap).le ⟨haL, pull_mono φ (rootA_le_antiUnipotent i) ha⟩
  exact mul_mem hf (ZP_le_F h ((A_inf_A_swap i).le ⟨ha, haA⟩))

theorem X_inf_X_swap (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ⊓ 𝐗[i.swap] = 𝐅 := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  have hxH : x ∈ 𝐇 :=
    (R_inf_R_swap h i).le ⟨(X_normal_R h i).1 hx1, (X_normal_R h i.swap).1 hx2⟩
  exact (L_inf_L_swap h i).le ⟨(X_inf_H h i).le ⟨hx1, hxH⟩, (X_inf_H h i.swap).le ⟨hx2, hxH⟩⟩

theorem X_inf_X (h : FCHyp L K n φ t) : 𝐗[Axis.one] ⊓ 𝐗[Axis.two] = 𝐅 :=
  X_inf_X_swap h Axis.one

theorem X_inf_centralizer (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    𝐗[i] ⊓ centralizer (𝐀[i.swap] : Set G) = 𝐅 := by
  refine le_antisymm (fun v hv => ?_) (le_inf le_sup_left fun f hf => mem_centralizer_iff.mpr
    fun b hb => (F_comm_A h hbt i.swap hf hb).symm)
  obtain ⟨hvX, hvC⟩ := mem_inf.mp hv
  have hvc : ∀ b ∈ 𝐀[i.swap], v * b = b * v := fun b hb =>
    (mem_centralizer_iff.mp hvC b hb).symm
  have hvN : v ∈ normalizer (𝐀[i.swap] : Set G) := mem_normalizer_of_conj_le fun b hb => by
    rw [hvc b hb, mul_inv_cancel_right]
    exact hb
  have hvH : v ∈ 𝐇 := (R_inf_normalizer_A h i).le ⟨(X_normal_R h i).1 hvX, hvN⟩
  have hvL : v ∈ 𝐋[i] := (X_inf_H h i).le ⟨hvX, hvH⟩
  rw [← SetLike.mem_coe, ← FullCenterWeyl.L_mul h i] at hvL
  obtain ⟨f, hf, a, ha, rfl⟩ := hvL
  have hac : ∀ b ∈ 𝐀[i.swap], a * b = b * a := fun b hb => by
    have h1 := hvc b hb
    have h2 := F_comm_A h hbt i.swap hf hb
    calc a * b = f⁻¹ * (f * a * b) := by group
      _ = f⁻¹ * (b * (f * a)) := by rw [h1]
      _ = f⁻¹ * (b * f) * a := by group
      _ = f⁻¹ * (f * b) * a := by rw [h2]
      _ = b * a := by group
  exact mul_mem hf (ZP_le_F h (mem_ZP_of_comm_A i ha hac))

theorem X_le_T (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ≤ 𝐓₀ := by
  cases i
  · exact (X_normal_R h _).1.trans le_sup_left
  · exact (X_normal_R h _).1.trans le_sup_right

theorem T_le_normalizer_X (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    𝐓₀ ≤ normalizer (𝐗[i] : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ hx => conj_T_mem_X h hbt i hg hx

theorem X_mul_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    (𝐗[Axis.one] : Set G) * (𝐗[Axis.two] : Set G) = 𝐒 :=
  (coe_mul_of_right_le_normalizer_left _ _
    ((X_le_T h Axis.two).trans (T_le_normalizer_X h hbt Axis.one))).symm

theorem card_S (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    Nat.card 𝐒 = Nat.card K ^ 8 := by
  have h1 := card_sup_mul_card_inf 𝐗[Axis.one] 𝐗[Axis.two]
    ((X_le_T h Axis.two).trans (T_le_normalizer_X h hbt Axis.one))
  rw [X_inf_X h, card_F h, card_X h Axis.one, card_X h Axis.two] at h1
  have hq : 0 < Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem card_T (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    Nat.card 𝐓₀ = 2 * Nat.card K ^ 8 := by
  have h1 := card_sup_mul_card_inf 𝐑[Axis.one] 𝐑[Axis.two] (R_le_normalizer_R h hbt Axis.one)
  rw [R_inf_R h, h.H_facts.2.2, card_R h Axis.one, card_R h Axis.two] at h1
  have hq : 0 < 2 * Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem S_inf_H (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐒 ⊓ 𝐇 = 𝐅 ⊔ 𝐏 := by
  have hLFP : ∀ i : Axis, 𝐋[i] ≤ 𝐅 ⊔ 𝐏 := fun i =>
    sup_le le_sup_left ((pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_right)
  refine le_antisymm (fun s hs => ?_) (le_inf (sup_le (le_sup_left.trans le_sup_left) ?_)
    (sup_le (F_le_H h) P_le_H))
  · obtain ⟨hsS, hsH⟩ := mem_inf.mp hs
    rw [← SetLike.mem_coe, ← X_mul_X h hbt] at hsS
    obtain ⟨x, hx, y, hy, rfl⟩ := hsS
    have hxR : x ∈ 𝐑[Axis.two] := by
      have := mul_mem (H_le_R h Axis.two hsH) (inv_mem ((X_normal_R h Axis.two).1 hy))
      rwa [mul_inv_cancel_right] at this
    have hxH : x ∈ 𝐇 := (R_inf_R h).le ⟨(X_normal_R h Axis.one).1 hx, hxR⟩
    have hyH : y ∈ 𝐇 := by
      have := mul_mem (inv_mem hxH) hsH
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (hLFP _ ((X_inf_H h _).le ⟨hx, hxH⟩)) (hLFP _ ((X_inf_H h _).le ⟨hy, hyH⟩))
  · rw [P_eq_A_sup_A]
    exact sup_le ((A_le_L _).trans ((L_le_X h _).trans le_sup_left))
      ((A_le_L _).trans ((L_le_X h _).trans le_sup_right))

theorem t_not_mem_S (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    t ∉ 𝐒 := fun ht => by
  have h1 : t ∈ 𝐒 ⊓ 𝐇 := ⟨ht, t_mem_H⟩
  rw [S_inf_H h hbt, ← Ks_eq h] at h1
  exact t_not_mem_Ks h h1

theorem S_le_T (h : FCHyp L K n φ t) : 𝐒 ≤ 𝐓₀ := sup_le (X_le_T h _) (X_le_T h _)

theorem T_le_normalizer_S (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) : 𝐓₀ ≤ normalizer (𝐒 : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_sup (fun _ hy => conj_T_mem_X h hbt _ hg hy)
    (fun _ hy => conj_T_mem_X h hbt _ hg hy) hx

theorem t_mem_T (h : FCHyp L K n φ t) : t ∈ 𝐓₀ := mem_sup_left (H_le_R h Axis.one t_mem_H)

theorem S_sup_t (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐒 ⊓ zpowers t = ⊥ ∧ 𝐒 ⊔ zpowers t = 𝐓₀ := by
  have hinf : 𝐒 ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxt⟩ := mem_inf.mp hx
    have hx' : x = 1 ∨ x = t := by
      obtain ⟨j, rfl⟩ := hxt
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact absurd hxS (t_not_mem_S h hbt)
  refine ⟨hinf, ?_⟩
  have hnorm : zpowers t ≤ normalizer (𝐒 : Set G) :=
    zpowers_le.mpr (T_le_normalizer_S h hbt (t_mem_T h))
  have h1 := card_sup_mul_card_inf 𝐒 (zpowers t) hnorm
  rw [hinf, card_bot, mul_one, card_S h hbt, Nat.card_zpowers, h.setup.order_t] at h1
  refine eq_of_le_of_card_ge (sup_le (S_le_T h) (zpowers_le.mpr (t_mem_T h))) ?_
  rw [card_T h hbt, h1, mul_comm]

theorem S_mul_t (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    (𝐒 : Set G) * (zpowers t : Set G) = 𝐓₀ := by
  rw [← (S_sup_t h hbt).2, coe_mul_of_right_le_normalizer_left _ _
    (zpowers_le.mpr (T_le_normalizer_S h hbt (t_mem_T h)))]

theorem F_comm_S (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {f : G} (hf : f ∈ 𝐅) {s : G} (hs : s ∈ 𝐒) : s * f = f * s := by
  have hle : 𝐒 ≤ centralizer ({f} : Set G) := sup_le
    (fun x hx => mem_centralizer_singleton_iff.mpr
      (comm_of_mul_self (fun _ hy => X_mul_self h hbt _ hy) hx (mem_sup_left hf)))
    (fun x hx => mem_centralizer_singleton_iff.mpr
      (comm_of_mul_self (fun _ hy => X_mul_self h hbt _ hy) hx (mem_sup_left hf)))
  exact mem_centralizer_singleton_iff.mp (hle hs)

theorem center_S (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    (center 𝐒).map 𝐒.subtype = 𝐅 := by
  refine le_antisymm (fun z hz => ?_) fun f hf => mem_center_map_iff.mpr
    ⟨(le_sup_left.trans le_sup_left : 𝐅 ≤ 𝐒) hf, fun s hs => F_comm_S h hbt hf hs⟩
  obtain ⟨hzS, hzc⟩ := mem_center_map_iff.mp hz
  rw [← SetLike.mem_coe, ← X_mul_X h hbt] at hzS
  obtain ⟨x, hx, y, hy, rfl⟩ := hzS
  have hxF : x ∈ 𝐅 := by
    refine (X_inf_centralizer h hbt Axis.one).le ⟨hx, mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hbX : b ∈ 𝐗[Axis.two] := L_le_X h Axis.two (A_le_L Axis.two hb)
    have h1 : b * (x * y) = x * y * b := hzc b (mem_sup_right hbX)
    have h2 : y * b = b * y := comm_of_mul_self (fun _ hw => X_mul_self h hbt _ hw) hy hbX
    calc b * x = b * (x * y) * y⁻¹ := by group
      _ = x * y * b * y⁻¹ := by rw [h1]
      _ = x * (y * b) * y⁻¹ := by group
      _ = x * (b * y) * y⁻¹ := by rw [h2]
      _ = x * b := by group
  exact (X_inf_centralizer h hbt Axis.two).le ⟨mul_mem (mem_sup_left hxF) hy,
    mem_centralizer_iff.mpr fun b hb =>
      hzc b (mem_sup_left (L_le_X h Axis.one (A_le_L Axis.one hb)))⟩

theorem comm_mem_F (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐗[Axis.one]) {y : G} (hy : y ∈ 𝐗[Axis.two]) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐅 := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ 𝐗[Axis.two] :=
    mul_mem (conj_T_mem_X h hbt _ (X_le_T h _ hx) hy) (inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ 𝐗[Axis.one] := by
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx (conj_T_mem_X h hbt _ (X_le_T h _ hy) (inv_mem hx))
  exact (X_inf_X h).le ⟨h2, h1⟩

theorem commutator_mem (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {s : G} (hs : s ∈ 𝐒) {s' : G} (hs' : s' ∈ 𝐒) : s * s' * s⁻¹ * s'⁻¹ ∈ 𝐅 := by
  rw [← SetLike.mem_coe, ← X_mul_X h hbt] at hs hs'
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hs
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hs'
  have hc : ∀ i : Axis, ∀ {x y : G}, x ∈ 𝐗[i] → y ∈ 𝐗[i] → x * y = y * x := fun i _ _ hx hy =>
    comm_of_mul_self (fun _ hw => X_mul_self h hbt i hw) hx hy
  obtain ⟨a, haF, ha⟩ : ∃ a ∈ 𝐅, x₂ * y₁ = a * y₁ * x₂ := by
    refine ⟨x₂ * y₁ * x₂⁻¹ * y₁⁻¹, ?_, by group⟩
    have := inv_mem (comm_mem_F h hbt hy₁ hx₂)
    rwa [show (y₁ * x₂ * y₁⁻¹ * x₂⁻¹)⁻¹ = x₂ * y₁ * x₂⁻¹ * y₁⁻¹ by group] at this
  obtain ⟨b, hbF, hb⟩ : ∃ b ∈ 𝐅, x₁ * y₂ = b * y₂ * x₁ :=
    ⟨x₁ * y₂ * x₁⁻¹ * y₂⁻¹, comm_mem_F h hbt hx₁ hy₂, by group⟩
  have e : x₁ * x₂ * (y₁ * y₂) = a * b * (y₁ * y₂ * (x₁ * x₂)) := by
    calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
      _ = x₁ * (a * y₁ * x₂) * y₂ := by rw [ha]
      _ = x₁ * a * y₁ * x₂ * y₂ := by group
      _ = a * x₁ * y₁ * x₂ * y₂ := by rw [hc _ hx₁ (mem_sup_left haF)]
      _ = a * (x₁ * y₁) * (x₂ * y₂) := by group
      _ = a * (y₁ * x₁) * (y₂ * x₂) := by rw [hc _ hx₁ hy₁, hc _ hx₂ hy₂]
      _ = a * y₁ * (x₁ * y₂) * x₂ := by group
      _ = a * y₁ * (b * y₂ * x₁) * x₂ := by rw [hb]
      _ = a * (y₁ * b) * y₂ * x₁ * x₂ := by group
      _ = a * (b * y₁) * y₂ * x₁ * x₂ := by rw [hc _ hy₁ (mem_sup_left hbF)]
      _ = a * b * (y₁ * y₂ * (x₁ * x₂)) := by group
  rw [e, show a * b * (y₁ * y₂ * (x₁ * x₂)) * (x₁ * x₂)⁻¹ * (y₁ * y₂)⁻¹ = a * b by group]
  exact mul_mem haF hbF


end Center

end BothTrivialHeisenberg

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise


end CFSG.LocalAnalysis.SymplecticFourStandard
