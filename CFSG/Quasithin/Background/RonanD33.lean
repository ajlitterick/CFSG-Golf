module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Quasithin.EmptyFaithful.S151S5A
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin.RonanD33

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isPGroup_iff_forall_mem {p : ℕ} {Y : Subgroup G} :
    IsPGroup p ↥Y ↔ ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k = 1 := by
  constructor
  · intro h y hy
    obtain ⟨k, hk⟩ := h ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro h ⟨y, hy⟩
    obtain ⟨k, hk⟩ := h y hy
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem pCoreOf_le (H : Subgroup G) : pCoreOf 2 H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_pCoreOf {H : Subgroup G} {x : G} :
    x ∈ pCoreOf 2 H ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pCoreOf_isPGroup (H : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 H) := by
  rw [isPGroup_iff_forall_mem]
  intro x hx
  obtain ⟨hxH, hxp⟩ := mem_pCoreOf.mp hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hxp⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hk
  simpa using this

theorem le_normalizer_pCoreOf (H : Subgroup G) : H ≤ normalizer (pCoreOf 2 H : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ pCoreOf 2 H, g * x * g⁻¹ ∈ pCoreOf 2 H := by
    intro g hg x hx
    obtain ⟨hxH, hxp⟩ := mem_pCoreOf.mp hx
    refine mem_pCoreOf.mpr ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), ?_⟩
    have h := (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem ⟨x, hxH⟩ hxp ⟨g, hg⟩
    exact h
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h := key g⁻¹ (H.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem isPGroup_subgroupOf {Y H : Subgroup G} (hY : IsPGroup 2 ↥Y) :
    IsPGroup 2 ↥(Y.subgroupOf H) := by
  rw [isPGroup_iff_forall_mem] at hY ⊢
  rintro ⟨y, hyH⟩ hy
  obtain ⟨k, hk⟩ := hY y hy
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem le_pCoreOf_of_le_normalizer {Y H : Subgroup G} (hYH : Y ≤ H)
    (hN : H ≤ normalizer (Y : Set G)) (hY : IsPGroup 2 ↥Y) : Y ≤ pCoreOf 2 H := by
  have hnorm : (Y.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hYH).mpr hN
  have hle : Y.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hnorm, isPGroup_subgroupOf hY⟩
  intro y hy
  exact mem_pCoreOf.mpr ⟨hYH hy, hle hy⟩

theorem conj_mem_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) {x : G} (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left (hA a ha)) (fun b hb => Subgroup.mem_sup_right (hB b hb))
  exact h hx


theorem le_normalizer_of_forall_conj_mem {S Y : Subgroup G} (h : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    S ≤ normalizer (Y : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h s hs y hy, fun hy => ?_⟩
  have h2 := h s⁻¹ (S.inv_mem hs) _ hy
  have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rwa [e] at h2

theorem mem_of_pow_mem_of_coprime {C : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ C) (hb : x ^ b ∈ C) : x ∈ C := by
  have hc : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  obtain ⟨u, v, huv⟩ := hc
  have h1 : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have e : (a : ℤ) * u + (b : ℤ) * v = 1 := by linarith
    rw [e, zpow_one]
  rw [h1]
  exact C.mul_mem (C.zpow_mem ha u) (C.zpow_mem hb v)


theorem pCoreOf_le_of_isSubnormal {H K : Subgroup G} (h : CFSG.Open.IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    have hHM : M ≤ normalizer (H : Set G) := (normal_subgroupOf_iff_le_normalizer hle).mp hN
    exact le_pCoreOf_of_le_normalizer ((pCoreOf_le H).trans hle)
      (hHM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup H)


theorem pCoreOf_le_of_sylow {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 ↥S)
    (hidx : ¬ 2 ∣ (S.subgroupOf H).index) : pCoreOf 2 H ≤ S := by
  have hS' : IsPGroup 2 ↥(S.subgroupOf H) := isPGroup_subgroupOf hS
  let P : Sylow 2 ↥H := hS'.toSylow hidx
  have h1 : CFSG.pCore 2 ↥H ≤ (P : Subgroup ↥H) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal P
  intro x hx
  obtain ⟨hxH, hxp⟩ := mem_pCoreOf.mp hx
  exact h1 hxp

theorem isQuasisimple_map_of_pCore_le_ker {G' : Type*} [Group G'] {L : Subgroup G} {ρ : G →* G'}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hker : pCoreOf 2 L ≤ ρ.ker) (hnt : ¬ L ≤ ρ.ker) : CFSG.IsQuasisimple ↥(L.map ρ) := by
  let ψ0 : ↥L →* G' := ρ.comp L.subtype
  have hψ : CFSG.pCore 2 ↥L ≤ ψ0.ker := by
    intro x hx
    have : (x : G) ∈ pCoreOf 2 L := mem_pCoreOf.mpr ⟨x.2, hx⟩
    exact hker this
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* G' := QuotientGroup.lift (CFSG.pCore 2 ↥L) ψ0 hψ
  have hψ_range : (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)).map ψ = L.map ρ := by
    ext g
    constructor
    · rintro ⟨y, -, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨QuotientGroup.mk ⟨l, hl⟩, Subgroup.mem_top _, rfl⟩
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  have hnt' : ¬ (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ ψ.ker := by
    intro h
    apply hnt
    intro l hl
    exact h (Subgroup.mem_top (QuotientGroup.mk ⟨l, hl⟩))
  have := CFSG.LocalCores.isQuasisimple_map hq' ψ hnt'
  rwa [hψ_range] at this


theorem mem_cComp_of_isQuasisimple_of_isSubnormal {K X : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hK : CFSG.Open.IsSubnormal K X) :
    K ∈ CFSG.Quasithin.cComp X := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, hK, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le hK
    have hsubK : CFSG.Open.IsSubnormal K' K :=
      CFSG.Quasithin.A3.subnormal_of_le_of_le hsub hlt.le hKX
    obtain ⟨P, hPK, hPn, hK'P⟩ := CFSG.Quasithin.A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)


end CFSG.Quasithin.RonanD33
