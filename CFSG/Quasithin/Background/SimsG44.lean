module

public import CFSG.Quasithin.Background.SimsG44Levi
public import CFSG.Quasithin.Background.SimsG45Basis
public import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

open Matrix CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

section Transvections

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] noncomputable def symplTransv (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (w : V) (μ : F) : V ≃ₗ[F] V :=
  LinearEquiv.transvection (f := μ • B.flip w) (v := w)
    (show μ • B w w = 0 by rw [halt, smul_zero])

variable (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)

theorem symplTransv_apply (w : V) (μ : F) (v : V) :
    symplTransv B halt w μ v = v + (μ * B v w) • w :=
  rfl

theorem symplTransv_mul (w : V) (μ ν : F) :
    symplTransv B halt w μ * symplTransv B halt w ν = symplTransv B halt w (μ + ν) := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, symplTransv_apply, symplTransv_apply, symplTransv_apply,
    LinearMap.map_add₂, LinearMap.map_smul₂, halt w, smul_eq_mul, mul_zero, add_zero]
  module

theorem symplTransv_coeff_zero (w : V) : symplTransv B halt w 0 = 1 :=
  LinearEquiv.ext fun v => by rw [symplTransv_apply, zero_mul, zero_smul, add_zero]; rfl


theorem symplTransv_inv (w : V) (μ : F) :
    (symplTransv B halt w μ)⁻¹ = symplTransv B halt w (-μ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [symplTransv_mul, add_neg_cancel, symplTransv_coeff_zero]

theorem symplTransv_mem_spGroup (w : V) (μ : F) : symplTransv B halt w μ ∈ spGroup B := by
  intro x y
  change B (symplTransv B halt w μ x) (symplTransv B halt w μ y) = B x y
  rw [symplTransv_apply, symplTransv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt w]
  rw [SimsG45.bilin_skew B halt w y]
  ring

variable (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include hnd

theorem commSpace_symplTransv {w : V} (hw : w ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    commSpace (symplTransv B halt w μ) = F ∙ w := by
  ext x
  change x ∈ LinearMap.range ((symplTransv B halt w μ : V →ₗ[F] V) - LinearMap.id) ↔ _
  simp only [LinearMap.mem_range, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    symplTransv_apply, add_sub_cancel_left, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y₀, hy₀⟩ := SimsG45.exists_pair_eq_one B halt hnd hw
    refine ⟨(a / μ) • y₀, ?_⟩
    rw [LinearMap.map_smul₂, hy₀, smul_eq_mul, mul_one]
    congr 1
    field_simp

theorem symplTransv_isTransv {w : V} (hw : w ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    IsTransv (symplTransv B halt w μ) := by
  refine ⟨?_, ?_⟩
  · have h := commSpace_symplTransv B halt hnd hw hμ
    rw [commSpace] at h
    rw [h, finrank_span_singleton hw]
  · refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      symplTransv_apply, add_sub_cancel_left, LinearMap.zero_apply, LinearMap.map_smul₂, halt w,
      smul_eq_mul, mul_zero, zero_smul]

end Transvections

section Stabilizer

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]


variable (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
  (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include halt hnd


end Stabilizer

section Basis

open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (exists_symplectic_basis_prescribed_pair)

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include halt hnd


end Basis

section Matrices

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (b : Module.Basis (Fin 4) F V)
  (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0)


end Matrices

section Generation

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
  (b : Module.Basis (Fin 4) F V)
  (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0)


end Generation

section Transport


end Transport

section RootGroup

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)

include hnd in
theorem mem_rootGroupHat_iff {d : V ≃ₗ[F] V} {u : V} (hu : u ≠ 0) (hcomm : commSpace d = F ∙ u)
    (g : V ≃ₗ[F] V) : g ∈ rootGroupHat B d ↔ ∃ μ : F, g = symplTransv B halt u μ := by
  let R : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {g | ∃ μ : F, g = symplTransv B halt u μ}
      mul_mem' := by
        rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
        exact ⟨μ + ν, symplTransv_mul B halt u μ ν⟩
      one_mem' := ⟨0, (symplTransv_coeff_zero B halt u).symm⟩
      inv_mem' := by
        rintro _ ⟨μ, rfl⟩
        exact ⟨-μ, symplTransv_inv B halt u μ⟩ }
  constructor
  · intro hg
    have hle : rootGroupHat B d ≤ R := by
      rw [rootGroupHat, Subgroup.closure_le]
      rintro e ⟨he, heT, hec⟩
      obtain ⟨w, -, μ, -, hev, hrange⟩ := SimsG45.exists_transv_form B halt hnd e he heT.1
      have hwu : F ∙ w = F ∙ u := hrange.symm.trans (hec.trans hcomm)
      have hw : w ∈ F ∙ u := hwu ▸ Submodule.mem_span_singleton_self w
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
      refine ⟨μ * a * a, LinearEquiv.ext fun v => ?_⟩
      rw [hev, symplTransv_apply, ← ha, LinearMap.map_smul, smul_eq_mul]
      module
    exact hle hg
  · rintro ⟨μ, rfl⟩
    by_cases hμ : μ = 0
    · rw [hμ, symplTransv_coeff_zero]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨symplTransv_mem_spGroup B halt u μ,
        symplTransv_isTransv B halt hnd hu hμ,
        by rw [commSpace_symplTransv B halt hnd hu hμ, hcomm]⟩

end RootGroup

section Parabolic


end Parabolic

section Main


end Main


end CFSG.Quasithin.SimsG4
