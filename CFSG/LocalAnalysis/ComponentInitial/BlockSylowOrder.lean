module

public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def normalizerConjHom (J : Subgroup G) : normalizer (J : Set G) →* MulAut J where
  toFun g := conjAut J g.2
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp [coe_conjAut])
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by simp [coe_conjAut, mul_assoc])

theorem coe_normalizerConjHom_apply (J : Subgroup G) (g : normalizer (J : Set G)) (x : J) :
    ((normalizerConjHom J g x : J) : G) = g * x * (g : G)⁻¹ := rfl

theorem ker_normalizerConjHom (J : Subgroup G) :
    (normalizerConjHom J).ker = (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := congrArg (fun σ : MulAut J => ((σ ⟨x, hx⟩ : J) : G)) h
    simp only [coe_normalizerConjHom_apply, MulAut.one_apply] at h1
    calc x * g = (g : G) * x * (g : G)⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_normalizerConjHom_apply, MulAut.one_apply, ← h x x.2, mul_inv_cancel_right]

theorem ker_centerQuotient_comp_normalizerConjHom (J : Subgroup G) [Group.IsPerfect J] :
    ((PerfectAutomorphisms.centerQuotientHom J).comp (normalizerConjHom J)).ker =
      (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := by
  rw [← ker_normalizerConjHom]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    exact PerfectAutomorphisms.centerQuotientHom_injective J (h.trans (map_one _).symm)
  · intro h
    rw [h, map_one]

theorem inner_le_range_centerQuotient_comp (J : Subgroup G) :
    OuterAutomorphisms.inner (J ⧸ center J) ≤
      ((PerfectAutomorphisms.centerQuotientHom J).comp (normalizerConjHom J)).range := by
  rintro _ ⟨τ, rfl⟩
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center J) τ
  refine ⟨⟨j, le_normalizer j.2⟩, ?_⟩
  rw [MonoidHom.comp_apply, ← centerQuotient_conj]
  congr 1

theorem card_dvd_card_mul_card_outer {T : Type*} [Group T] [Finite T] (hT : center T = ⊥)
    {A : Subgroup (MulAut T)} (hA : OuterAutomorphisms.inner T ≤ A) :
    Nat.card A ∣ Nat.card T * Nat.card (Outer T) := by
  set f := (QuotientGroup.mk' (OuterAutomorphisms.inner T)).comp A.subtype with hf
  have hker : f.ker.map A.subtype = OuterAutomorphisms.inner T := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hτ)
    · intro hσ
      exact ⟨⟨σ, hA hσ⟩, MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 hσ), rfl⟩
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgc : g ∈ center T := mem_center_iff.2 fun y => by
      have := congrArg (fun σ : MulAut T => σ y) (MonoidHom.mem_ker.1 hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hT] at hgc
    exact hgc
  have hinner : Nat.card (OuterAutomorphisms.inner T) = Nat.card T := by
    rw [OuterAutomorphisms.inner, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← Subgroup.card_map_of_injective A.subtype_injective, hker, hinner] at h1
  rw [h1, mul_comm]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_subgroup_dvd_card f.range)

variable [Finite G]


omit [Finite G] in
theorem conjSub_eq_mulAut_smul (g : G) (K : Subgroup G) : conjSub g K = MulAut.conj g • K := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  rfl

omit [Finite G] in
theorem map_subtype_conjSub (H : Subgroup G) (h : H) (S : Subgroup H) :
    (conjSub h S).map H.subtype = conjSub (h : G) (S.map H.subtype) := by
  rw [conjSub, conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1


end CFSG.LocalAnalysis.ComponentInitial
