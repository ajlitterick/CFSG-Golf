module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardRoot
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardTorus
public import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RootStandard

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem exists_sylow_map_iff [Finite G] {p : ℕ} [Fact p.Prime] {X Y : Subgroup G} :
    (∃ R : Sylow p ↥X, (R : Subgroup ↥X).map X.subtype = Y) ↔
      Y ≤ X ∧ IsPGroup p Y ∧ ¬ p ∣ Y.relIndex X := by
  constructor
  · rintro ⟨R, rfl⟩
    refine ⟨map_subtype_le _, R.isPGroup'.map _, ?_⟩
    rw [relIndex, subgroupOf, comap_map_eq_self_of_injective X.subtype_injective]
    exact R.not_dvd_index
  · rintro ⟨hYX, hY, hidx⟩
    have hY' : IsPGroup p (Y.subgroupOf X) := hY.comap_of_injective X.subtype X.subtype_injective
    refine ⟨hY'.toSylow hidx, ?_⟩
    change (Y.subgroupOf X).map X.subtype = Y
    rw [subgroupOf_map_subtype, inf_of_le_left hYX]

theorem exists_sylow_subgroupOf_iff [Finite G] {p : ℕ} [Fact p.Prime] {H X Y : Subgroup G}
    (hXH : X ≤ H) (hYX : Y ≤ X) :
    (∃ R : Sylow p ↥(X.subgroupOf H),
        (R : Subgroup ↥(X.subgroupOf H)).map (X.subgroupOf H).subtype = Y.subgroupOf H) ↔
      ∃ R : Sylow p ↥X, (R : Subgroup ↥X).map X.subtype = Y := by
  rw [exists_sylow_map_iff, exists_sylow_map_iff, relIndex_subgroupOf hXH]
  have hYH : Y ≤ H := hYX.trans hXH
  have hp : IsPGroup p (Y.subgroupOf H) ↔ IsPGroup p Y :=
    ⟨fun h => h.of_equiv (subgroupOfEquivOfLe hYH),
      fun h => h.of_equiv (subgroupOfEquivOfLe hYH).symm⟩
  rw [hp]
  exact ⟨fun h => ⟨hYX, h.2⟩, fun h =>
    ⟨fun x hx => mem_subgroupOf.mpr (hYX (mem_subgroupOf.mp hx)), h.2⟩⟩

theorem isQuasisimple_of_sl2 {K : Type} [Field K] [CharP K 2] [Finite K] (hK : 4 ≤ Nat.card K)
    {X : Type*} [Group X] (e : SL₂ K ≃* X) : CFSG.Assembly.IsQuasisimple X := by
  have : Group.IsPerfect (SL₂ K) := sl2_isPerfect hK
  have : IsSimpleGroup (SL₂ K) := sl2_isSimpleGroup hK
  have hc : center X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ center (SL₂ K) := mem_center_iff.mpr fun y => by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact mem_center_iff.mp hz (e y)
    rw [sl2_center_eq_bot, mem_bot] at hz'
    rw [mem_bot]
    simpa using congrArg e hz'
  refine ⟨(Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top, ?_⟩
  exact (((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans
    e.symm).isSimpleGroup

end General

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {t : G} (φ : L ≃* antiSp K)

local notation "𝐔[" k "]" => pull φ (rootU K k)
local notation "𝐉[" k "]" => pull φ (axisTorus K k)
set_option quotPrecheck false in
local notation "𝐒[" k "]" => (⁅L ⊓ centralizer (𝐉[k] : Set G),
  L ⊓ centralizer (𝐉[k] : Set G)⁆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐇𝐭[" k "]" => centralizer (𝐉[k] : Set G)

omit [Finite G] [CharP K 2] [Finite K] in
theorem t_mem_Ht (hS : TwoCoreSetup L K n t) (k : Axis) : t ∈ 𝐇𝐭[k] :=
  mem_centralizer_iff.mpr fun _ hb => (hS.comm (pull_le φ _ hb)).symm

omit [Finite G] [CharP K 2] [Finite K] in
theorem S_le_Ht (k : Axis) : 𝐒[k] ≤ 𝐇𝐭[k] := (S_le_CL φ k).trans inf_le_right

omit [Finite G] [Finite K] in
theorem U_comm_mul_self {k : Axis} {x y : G} (hx : x ∈ 𝐔[k]) (hy : y ∈ 𝐔[k]) :
    x * y = y * x ∧ x * x = 1 := by
  obtain ⟨a, rfl⟩ := exists_coordG_eq φ k hx
  obtain ⟨b, rfl⟩ := exists_coordG_eq φ k hy
  refine ⟨by rw [← coordG_add, ← coordG_add, add_comm], ?_⟩
  rw [← coordG_add, CharTwo.add_self_eq_zero, coordG_zero]

theorem exists_four_S {n : ℕ} (hn : 2 ≤ n) (hKn : Nat.card K = 2 ^ n) (k : Axis) :
    ∃ E : Subgroup ↥𝐇𝐭[k], E ≤ 𝐒[k].subgroupOf 𝐇𝐭[k] ∧
      CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have hK : 4 ≤ Nat.card K := by
    rw [hKn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdvd : 2 ^ 2 ∣ Nat.card 𝐔[k] := by
    rw [card_U, hKn]
    exact pow_dvd_pow 2 hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hUS := U_le_S φ hK k
  have hle : E₀.map 𝐔[k].subtype ≤ 𝐇𝐭[k] := (map_subtype_le _).trans (hUS.trans (S_le_Ht φ k))
  refine ⟨(E₀.map 𝐔[k].subtype).subgroupOf 𝐇𝐭[k], fun x hx => mem_subgroupOf.mpr
    (hUS (map_subtype_le _ (mem_subgroupOf.mp hx))), ⟨⟨⟨fun x y => Subtype.ext
    (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
  · have hx := map_subtype_le E₀ (mem_subgroupOf.mp x.2)
    have hy := map_subtype_le E₀ (mem_subgroupOf.mp y.2)
    exact (U_comm_mul_self φ hx hy).1
  · have hx' := map_subtype_le E₀ (mem_subgroupOf.mp hx)
    rw [SubgroupClass.coe_pow, pow_two]
    exact (U_comm_mul_self φ hx' hx').2
  · rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      card_map_of_injective 𝐔[k].subtype_injective, hE₀]
    norm_num


end Standard

section Closure

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}
set_option quotPrecheck false in
local notation "𝐕[" i "," k "]" => (𝐌₀[i] ⊓ centralizer (𝐉[k] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒[" k "]" => (⁅L ⊓ centralizer (𝐉[k] : Set G),
  L ⊓ centralizer (𝐉[k] : Set G)⁆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇𝐭[" k "]" => centralizer (𝐉[k] : Set G)
set_option quotPrecheck false in
local notation "𝐘[" k "]" => closure {x : G | ∃ g ∈ 𝐇𝐭[k], ∃ s ∈ 𝐒[k], x = g⁻¹ * s * g}

omit [Finite G] [CharP K 2] [Finite K] in
theorem Y_le_H (k : Axis) : 𝐘[k] ≤ 𝐇𝐭[k] := by
  rw [closure_le]
  rintro _ ⟨g, hg, s, hs, rfl⟩
  exact mul_mem (mul_mem (inv_mem hg) (S_le_Ht φ k hs)) hg

omit [Finite G] [CharP K 2] [Finite K] in
theorem S_le_Y (k : Axis) : 𝐒[k] ≤ 𝐘[k] := fun s hs =>
  subset_closure ⟨1, one_mem _, s, hs, by group⟩

omit [Finite G] [CharP K 2] [Finite K] in
theorem conj_mem_Y (k : Axis) {g : G} (hg : g ∈ 𝐇𝐭[k]) {y : G} (hy : y ∈ 𝐘[k]) :
    g * y * g⁻¹ ∈ 𝐘[k] := by
  have hle : 𝐘[k] ≤ (𝐘[k]).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro _ ⟨h₀, hh₀, s, hs, rfl⟩
    refine subset_closure ⟨h₀ * g⁻¹, mul_mem hh₀ (inv_mem hg), s, hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle hy

omit [Finite G] in
theorem isPerfect_Y (hK : 4 ≤ Nat.card K) (k : Axis) : Group.IsPerfect 𝐘[k] := by
  have hS : ⁅𝐒[k], 𝐒[k]⁆ = 𝐒[k] := by
    have : Group.IsPerfect (SL₂ K) := sl2_isPerfect hK
    have : Group.IsPerfect (rootHom φ k).range := Group.IsPerfect.range _
    rw [S_eq φ hK]
    exact Subgroup.commutator_eq_self
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
  rw [closure_le]
  rintro _ ⟨g, hg, s, hs, rfl⟩
  have hmap : 𝐒[k].map (MulAut.conj g⁻¹).toMonoidHom ≤ 𝐘[k] := by
    rintro _ ⟨s', hs', rfl⟩
    refine subset_closure ⟨g, hg, s', hs', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hmem : g⁻¹ * s * g ∈ (⁅𝐒[k], 𝐒[k]⁆ : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hS]
    exact ⟨s, hs, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  rw [Subgroup.map_commutator] at hmem
  exact commutator_mono hmap hmap hmem

theorem V_inf_centralizer (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    𝐕[i, k] ⊓ centralizer (𝐉[k.swap] : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxJ'⟩ := mem_inf.mp hx
  obtain ⟨hxM, hxJ⟩ := mem_inf.mp hxV
  obtain ⟨j₀, hj₀⟩ := exists_goodTorus h
  have hc := mem_centralizer_iff.mp (mem_centralizer_J0 k hxJ hxJ') j₀ hj₀.mem
  refine (mem_bot).mpr (eq_one_of_mem_M_of_fix h i hne hbot hj₀ hxM ?_)
  rw [mul_assoc, ← hc, inv_mul_cancel_left]

theorem V_le_Y (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐕[i, k] ≤ 𝐘[k] := by
  have hK : 4 ≤ Nat.card K := h.four_le_card
  intro x hx
  have hJV : 𝐉[k.swap] ≤ normalizer (𝐕[i, k] : Set G) := fun z hz =>
    J_le_normalizer_V h i hne hbot k (axisTorus_le_J0 _ hz)
  obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_coprime Nat.prime_two hJV
    ((isPGroup_M h i hne hbot).to_le inf_le_left) (not_two_dvd_card_J h k.swap) hx
  have hc1 : c = 1 := by
    have := hc
    rwa [V_inf_centralizer h i hne hbot k, mem_bot] at this
  rw [hc1, mul_one]
  refine (closure_le _).mpr ?_ hd
  rintro _ ⟨q, hq, z, hz, rfl⟩
  obtain ⟨hqM, hqJ⟩ := mem_inf.mp hq
  obtain ⟨b, hb, s, hs, rfl⟩ := exists_torus_decomp φ hK k (axisTorus_le_J0 _ hz)
  have hbq : Commute b q := mem_centralizer_iff.mp hqJ b hb
  have hbs : Commute b s := J_comm_S φ k hb hs
  have e : q⁻¹ * (b * s * q * (b * s)⁻¹) = (q⁻¹ * s * q) * s⁻¹ := by
    have h1 : b * (s * q * s⁻¹) = s * q * s⁻¹ * b :=
      ((hbs.mul_right hbq).mul_right hbs.inv_right).eq
    calc q⁻¹ * (b * s * q * (b * s)⁻¹) = q⁻¹ * ((b * (s * q * s⁻¹)) * b⁻¹) := by group
      _ = q⁻¹ * s * q * s⁻¹ := by rw [h1]; group
      _ = (q⁻¹ * s * q) * s⁻¹ := by group
  rw [e]
  exact mul_mem (subset_closure ⟨q, hqJ, s, hs, rfl⟩) (S_le_Y k (inv_mem hs))

theorem card_V_ge (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : Nat.card K ^ 2 ≤ Nat.card 𝐕[i, k] :=
  (card_W h k).symm.le.trans (Subgroup.card_le_of_le (W_le_V h i hne hbot k))


theorem exists_W_kappa (h : FCHyp L K n φ t) (k : Axis) {u : G} (hu : u ∈ 𝐔[k]) :
    ∃ w ∈ 𝐖[k], t⁻¹ * (w⁻¹ * t * w) = u ∧ w⁻¹ * t * w = t * u ∧ w * u = u * w := by
  obtain ⟨w, hw, hwu⟩ := exists_kappa_eq_W h k hu
  refine ⟨w, hw, hwu, by rw [← hwu, mul_inv_cancel_left], ?_⟩
  exact comm_ZP h (F_le_H h (W_le_F k hw)) (pull_mono φ (rootU_le_center k) hu)


end Closure

end RootStandard

end CFSG.LocalAnalysis.SymplecticFourStandard
