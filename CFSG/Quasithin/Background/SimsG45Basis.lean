module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.Quasithin.SimsG45

open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.UnbalancedCatalog

variable {F : Type} [Field F] {V : Type*} [AddCommGroup V] [Module F V]


theorem toMatrix_eq_minorJ (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) :
    BilinForm.toMatrix b B = SpChain.minorJ F := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, hb, SpChain.minorJ_apply]

theorem mem_isometryGroup_iff_mem_antiSp (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (g : V ≃ₗ[F] V) :
    g ∈ isometryGroup B ↔ basisMatrixEquiv b g ∈ SpChain.antiSp F := by
  have h := isometry_iff_matrix b B g
  rw [toMatrix_eq_minorJ B b hb] at h
  exact h.trans SpChain.mem_antiSp.symm

@[expose] noncomputable def isoAntiSp (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) :
    isometryGroup B ≃* SpChain.antiSp F where
  toFun g := ⟨basisMatrixEquiv b g.1, (mem_isometryGroup_iff_mem_antiSp B b hb g.1).mp g.2⟩
  invFun A := ⟨(basisMatrixEquiv b).symm A.1,
    (mem_isometryGroup_iff_mem_antiSp B b hb _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact A.2)⟩
  left_inv g := Subtype.ext ((basisMatrixEquiv b).symm_apply_apply g.1)
  right_inv A := Subtype.ext ((basisMatrixEquiv b).apply_symm_apply A.1)
  map_mul' g h := Subtype.ext ((basisMatrixEquiv b).map_mul g.1 h.1)

@[simp]
theorem coe_isoAntiSp (B : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (g : isometryGroup B) :
    ((isoAntiSp B b hb g : SpChain.antiSp F) : Matrix.GeneralLinearGroup (Fin 4) F) =
      basisMatrixEquiv b (g : V ≃ₗ[F] V) := rfl


end CFSG.Quasithin.SimsG45
