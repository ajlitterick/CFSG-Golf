module

import Mathlib.Data.ZMod.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Roots

import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Refl
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRootsAux
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLiftAux
import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
import CFSG.Mathlib.Decide.Bounded

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open Certificates.OmegaSevenMax
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega.E7RootSet

private theorem p13wAux_bilin_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.Nondegenerate) {u : V} (hu : u ≠ 0) :
    B u ≠ 0 := by
  intro h
  apply hu
  apply hB.1 u
  intro y
  rw [h]
  simp

private theorem p13wAux_ne_zero_of_bilin_self {V : Type*} [AddCommGroup V]
    [Module (ZMod 3) V] (B : LinearMap.BilinForm (ZMod 3) V) {v : V} (hv : B v v ≠ 0) :
    v ≠ 0 := by
  intro h
  apply hv
  rw [h]
  simp

private theorem p13wAux_finrank_ker {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (f : V →ₗ[F] F) (hf : f ≠ 0) :
    Module.finrank F (LinearMap.ker f) + 1 = Module.finrank F V := by
  have htop : LinearMap.range f = ⊤ := Module.Dual.range_eq_top_of_ne_zero hf
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, _root_.finrank_top, Module.finrank_self] at h
  omega

private theorem p13wAux_ker_eq_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) {ψ v : V} (hψ : ψ ≠ 0) (hv : B v v ≠ 0)
    (hle : ∀ x, B ψ x = 0 → B v x = 0) :
    LinearMap.ker (B ψ) = LinearMap.ker (B v) := by
  have hBψ : B ψ ≠ 0 := p13wAux_bilin_ne_zero B hB hψ
  have hBv : B v ≠ 0 :=
    p13wAux_bilin_ne_zero B hB (p13wAux_ne_zero_of_bilin_self B hv)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro x hx
    exact hle x (LinearMap.mem_ker.mp hx)
  · have h1 := p13wAux_finrank_ker (B ψ) hBψ
    have h2 := p13wAux_finrank_ker (B v) hBv
    omega

private theorem p13wAux_smul_of_ker_eq {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.Nondegenerate)
    (hsymm : ∀ x y, B x y = B y x) {ψ v : V} (hv : B v v ≠ 0)
    (hker : LinearMap.ker (B ψ) = LinearMap.ker (B v)) :
    ∃ c : ZMod 3, c ≠ 0 ∧ ψ = c • v := by
  have hv0 : v ≠ 0 := p13wAux_ne_zero_of_bilin_self B hv
  have hBv : B v ≠ 0 := p13wAux_bilin_ne_zero B hB hv0
  obtain ⟨y, hvy⟩ : ∃ y, B v y ≠ 0 := by
    by_contra h
    apply hBv
    ext z
    by_contra hz
    exact h ⟨z, hz⟩
  have hBψy : B ψ y ≠ 0 := by
    intro h0
    apply hvy
    have hmem : y ∈ LinearMap.ker (B v) := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr h0
    exact LinearMap.mem_ker.mp hmem
  have hsmul : B ψ = (B ψ y / B v y) • B v := by
    ext z
    have hz : B v (z - (B v z / B v y) • y) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, _root_.div_mul_cancel₀ (B v z) hvy]
      exact _root_.sub_self _
    have hzψ : B ψ (z - (B v z / B v y) • y) = 0 := by
      have hmem : z - (B v z / B v y) • y ∈ LinearMap.ker (B v) :=
        LinearMap.mem_ker.mpr hz
      rw [← hker] at hmem
      exact LinearMap.mem_ker.mp hmem
    have hzψ' : B ψ z = (B v z / B v y) * B ψ y := by
      have h := hzψ
      rw [map_sub, map_smul, smul_eq_mul] at h
      exact _root_.sub_eq_zero.mp h
    have hexp : B ψ z = (B ψ y / B v y) * B v z := by
      rw [hzψ', div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm (B v z) (B ψ y)]
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact hexp
  refine ⟨B ψ y / B v y, div_ne_zero hBψy hvy, ?_⟩
  have hzero : ∀ x : V, B x (ψ - (B ψ y / B v y) • v) = 0 := by
    intro x
    have hx := congrArg (fun f => f x) hsmul
    simp only [LinearMap.smul_apply, smul_eq_mul] at hx
    rw [map_sub, map_smul, smul_eq_mul, hsymm x ψ, hsymm x v, hx]
    exact _root_.sub_self _
  exact sub_eq_zero.mp (hB.2 (ψ - (B ψ y / B v y) • v) hzero)

private theorem p13wAux_smul_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x) {ψ v : V} (hψ : ψ ≠ 0)
    (hv : B v v ≠ 0) (hle : ∀ x, B ψ x = 0 → B v x = 0) :
    ∃ c : ZMod 3, c ≠ 0 ∧ ψ = c • v :=
  p13wAux_smul_of_ker_eq B hB hsymm hv (p13wAux_ker_eq_of_le B hB hψ hv hle)

private theorem p13wAux_pm_one (c : ZMod 3) (hc : c ≠ 0) : c = 1 ∨ c = -1 := by
  revert c
  decide +kernel


private noncomputable def p13wAux_e7B : LinearMap.BilinForm (ZMod 3) V :=
  QuadraticMap.polarBilin qForm

private theorem p13wAux_e7B_apply (x y : V) : p13wAux_e7B x y = polarV x y := by
  rw [p13wAux_e7B, QuadraticMap.polarBilin_apply_apply, polar_qForm]

private def p13wAux_e7Codes : List ℕ :=
  CFSG.StandardType.e7RootsP1_certVecs.map fun v => encV (redV v)

open scoped CFSG.Decide.Bounded in
private theorem p13wAux_E7_finite :
    ∀ c ∈ List.range 2187,
      polarV (decV c) (decV c) ≠ 0 →
      (∀ j : Fin 7,
        encV ((Pi.single j (1 : ZMod 3) : V) -
          (2 * polarV (Pi.single j (1 : ZMod 3)) (decV c) /
            polarV (decV c) (decV c)) • decV c) ∈ p13wAux_e7Codes) →
      encV (decV c) ∈ p13wAux_e7Codes := by
  decide +kernel

private theorem p13wAux_redV_single :
    ∀ j : Fin 7, redV (Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ) =
      (Pi.single j (1 : ZMod 3) : V) := by
  decide +kernel

private theorem p13wAux_e7_mem_codes
    (x : V) :
    x ∈ rootSet ↔ encV x ∈ p13wAux_e7Codes := by
  constructor
  · intro hx
    have hx' : x ∈ (↑rootSet : Set V) := by simpa using hx
    rw [rootSet_eq_image] at hx'
    obtain ⟨α, hα, rfl⟩ := hx'
    exact List.mem_map.mpr ⟨α, (CFSG.StandardType.e7RootsP1_isRoot_iff α).mp hα, rfl⟩
  · intro hx
    obtain ⟨α, hα, hαx⟩ := List.mem_map.mp hx
    have hred : redV α = x := by
      have := congrArg decV hαx
      simpa [decV_encV] using this
    have hroot : redV α ∈ rootSet := by
      rw [mem_rootSet_iff]
      exact ⟨α, (CFSG.StandardType.e7RootsP1_isRoot_iff α).mpr hα, rfl⟩
    rwa [hred] at hroot

theorem p13a3_E7_pointwise_stabilizer
    (ψ : V) (hψ : ψ ≠ 0) (w : WeylGroup Tag.E7)
    (hw : ∀ x : V, polarV ψ x = 0 → rhoEquiv w x = x) :
    w = 1 ∨ ∃ β, IsRoot Tag.E7 β ∧ (redV β = ψ ∨ redV β = -ψ) ∧ w = rootReflection β := by
  classical
  have hB : p13wAux_e7B.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr e7QForm_nondegenerate
  have hBsymm : p13wAux_e7B.IsSymm := QuadraticMap.isSymm_polarBilin qForm
  have hsymm : ∀ x y : V, p13wAux_e7B x y = p13wAux_e7B y x := fun x y => hBsymm.eq x y
  have hBapply : ∀ x y : V, p13wAux_e7B x y = polarV x y := p13wAux_e7B_apply
  have hpolar_comm : ∀ x y : V, polarV x y = polarV y x := by
    intro x y
    rw [← polar_qForm x y, ← polar_qForm y x]
    exact QuadraticMap.polar_comm (⇑qForm) x y
  have horth : ∀ z : V, qForm (rhoEquiv w z) = qForm z := by
    have hmem := rhoEquiv_mem (w := w)
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hmem
    exact hmem
  have hg : ∀ x y : V, p13wAux_e7B (rhoEquiv w x) (rhoEquiv w y) = p13wAux_e7B x y := by
    intro x y
    rw [hBapply, hBapply, ← polar_qForm, ← polar_qForm]
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, horth, horth, horth]
  have hfixH : ∀ x ∈ LinearMap.ker (p13wAux_e7B ψ), rhoEquiv w x = x := by
    intro x hx
    have hx' : p13wAux_e7B ψ x = 0 := LinearMap.mem_ker.mp hx
    rw [hBapply] at hx'
    exact hw x hx'
  have hBψ : p13wAux_e7B ψ ≠ 0 := p13wAux_bilin_ne_zero p13wAux_e7B hB hψ
  have hH : Module.finrank (ZMod 3) (LinearMap.ker (p13wAux_e7B ψ)) + 1 =
      Module.finrank (ZMod 3) V :=
    p13wAux_finrank_ker (p13wAux_e7B ψ) hBψ
  rcases P13a1_hyperplane_fixer (F := ZMod 3) (by decide : (2 : ZMod 3) ≠ 0)
      p13wAux_e7B hB hBsymm (rhoEquiv w) hg (LinearMap.ker (p13wAux_e7B ψ)) hH hfixH with
    hrefl | ⟨v, hv, hform⟩
  · left
    apply rho_injective
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := redV_surj x
    rw [rho_apply_redV, rho_apply_redV]
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (redV y)) hrefl
    rw [rhoEquiv_redV] at h
    simpa using h
  · right
    have hform' : ∀ x : V, rhoEquiv w x =
        x - (2 * polarV x v / polarV v v) • v := by
      intro x
      rw [hform x, hBapply x v, hBapply v v]
    have hpolarvv : polarV v v ≠ 0 := by
      intro h
      exact hv (by rw [hBapply]; exact h)
    have hsimple : ∀ j : Fin 7, (Pi.single j (1 : ZMod 3) : V) ∈ rootSet := by
      intro j
      rw [mem_rootSet_iff]
      exact ⟨(Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ), IsRoot.basis (τ := Tag.E7) j,
        p13wAux_redV_single j⟩
    have hmem_image : ∀ j : Fin 7,
        rhoEquiv w (Pi.single j (1 : ZMod 3)) ∈ rootSet := by
      intro j
      rw [← rho_image_rootSet w]
      exact Finset.mem_image.mpr ⟨_, hsimple j, rfl⟩
    have hcode : ∀ j : Fin 7,
        encV ((Pi.single j (1 : ZMod 3) : V) -
          (2 * polarV (Pi.single j (1 : ZMod 3)) v / polarV v v) • v) ∈
          p13wAux_e7Codes := by
      intro j
      rw [← p13wAux_e7_mem_codes]
      rw [← hform' (Pi.single j (1 : ZMod 3))]
      exact hmem_image j
    have hvcodes : encV v ∈ p13wAux_e7Codes := by
      have hmain := p13wAux_E7_finite (encV v) (List.mem_range.mpr (encV_lt v)) ?_ ?_
      · simpa [decV_encV] using hmain
      · rw [decV_encV]
        exact hpolarvv
      · intro j
        simpa [decV_encV] using hcode j
    have hvroot : v ∈ rootSet := (p13wAux_e7_mem_codes v).mpr hvcodes
    obtain ⟨β, hβ, hβv⟩ := mem_rootSet_iff.mp hvroot
    have hle : ∀ x : V, p13wAux_e7B ψ x = 0 → p13wAux_e7B v x = 0 := by
      intro x hx
      have hxfix : rhoEquiv w x = x := hfixH x hx
      rw [hform' x] at hxfix
      have hzero : (2 * polarV x v / polarV v v) • v = 0 := sub_eq_self.mp hxfix
      have hcoef : 2 * polarV x v / polarV v v = 0 := by
        rcases smul_eq_zero.mp hzero with h | h
        · exact h
        · exact absurd h (p13wAux_ne_zero_of_bilin_self p13wAux_e7B hv)
      have h2 : 2 * polarV x v = 0 := by
        rcases div_eq_zero_iff.mp hcoef with h | h
        · exact h
        · exact absurd h hpolarvv
      have hxv : polarV x v = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h (by decide : (2 : ZMod 3) ≠ 0)
        · exact h
      rw [hBapply, hpolar_comm]
      exact hxv
    obtain ⟨c, hc, hψcv⟩ :=
      p13wAux_smul_of_le p13wAux_e7B hB hsymm hψ hv hle
    have hβsign : redV β = ψ ∨ redV β = -ψ := by
      rcases p13wAux_pm_one c hc with hc1 | hcneg
      · left
        rw [hβv, hψcv, hc1, one_smul]
      · right
        rw [hβv, hψcv, hcneg]
        simp
    have hbb : CFSG.LieType.Steinberg.Adjoint.iform β β = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
        (Or.inr (Or.inr (Or.inl rfl))) hβ
    have hscalar : ∀ y : Fin Tag.E7.rank → ℤ,
        ((corootPair β y : ℤ) : ZMod 3) =
          2 * polarV (redV y) (redV β) / polarV (redV β) (redV β) := by
      intro y
      have hcor : corootPair β y = CFSG.LieType.Steinberg.Adjoint.iform β y := by
        rw [corootPair, hbb]
        exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)
      have hp1 : polarV (redV y) (redV β) =
          ((CFSG.LieType.Steinberg.Adjoint.iform y β : ℤ) : ZMod 3) := by
        rw [← polar_qForm, CFSG.StandardType.e7LiftP11_polarV_redV]
      have hp2 : polarV (redV β) (redV β) = (2 : ZMod 3) := by
        rw [← polar_qForm, CFSG.StandardType.e7LiftP11_polarV_redV, hbb]
        norm_num
      rw [hcor, hp1, hp2, CFSG.LieType.Steinberg.Adjoint.iform_comm β y]
      rw [mul_comm (2 : ZMod 3)
          ((CFSG.LieType.Steinberg.Adjoint.iform y β : ℤ) : ZMod 3),
        mul_div_cancel_right₀ _ (by decide : (2 : ZMod 3) ≠ 0)]
    have hformβ : ∀ x : V, rhoEquiv w x =
        x - (2 * polarV x (redV β) / polarV (redV β) (redV β)) • redV β := by
      intro x
      rw [hform' x, ← hβv]
    have hbase : ∀ y : Fin Tag.E7.rank → ℤ,
        rhoEquiv (rootReflection β) (redV y) = rhoEquiv w (redV y) := by
      intro y
      calc rhoEquiv (rootReflection β) (redV y)
          = redV (rootReflection β • y) := rhoEquiv_redV _ _
        _ = redV (y - corootPair β y • β) := by rw [rootReflection_smul hβ]
        _ = redV y - ((corootPair β y : ℤ) : ZMod 3) • redV β := by
              rw [redV_sub, redV_zsmul]
        _ = redV y - (2 * polarV (redV y) (redV β) /
              polarV (redV β) (redV β)) • redV β := by rw [hscalar]
        _ = rhoEquiv w (redV y) := (hformβ (redV y)).symm
    have hrooteq : rhoEquiv (rootReflection β) = rhoEquiv w := by
      apply LinearEquiv.ext
      intro x
      obtain ⟨y, rfl⟩ := redV_surj x
      exact hbase y
    refine ⟨β, hβ, hβsign, ?_⟩
    have hrmem : (rho (rootReflection β) :
        CFSG.OddStandard.SmallF3.Omega.OGroup qForm) = rho w := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      obtain ⟨y, rfl⟩ := redV_surj x
      rw [rho_apply_redV, rho_apply_redV]
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (redV y)) hrooteq
      rw [rhoEquiv_redV, rhoEquiv_redV] at h
      simpa using h
    exact (rho_injective hrmem).symm


end CFSG.StandardType.FrameRoute
