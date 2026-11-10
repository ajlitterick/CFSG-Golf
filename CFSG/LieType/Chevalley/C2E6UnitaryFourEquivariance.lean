module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourCompound
import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem Pf_param_aux : ∀ a b c d e f : ZMod 2,
    Pf (param ![a, b, c, d, e, f]) = algebraMap (ZMod 2) K (Q ![a, b, c, d, e, f]) := by
  decide

theorem Pf_param (x : X) : Pf (param x) = algebraMap (ZMod 2) K (Q x) := by
  rw [eta_X x]
  exact Pf_param_aux _ _ _ _ _ _

theorem Pf_eq_Q {w : W} (hw : w ∈ W₀) : Pf w = algebraMap (ZMod 2) K (Q (psiLin w)) := by
  conv_lhs => rw [← param_psiLin hw]
  exact Pf_param _

theorem algebraMap_injective : Function.Injective (algebraMap (ZMod 2) K) :=
  (algebraMap (ZMod 2) K).injective

@[expose] def paramLin : X →ₗ[ZMod 2] W := W₀.subtype ∘ₗ (Ψ.symm : X →ₗ[ZMod 2] W₀)

theorem paramLin_apply (x : X) : paramLin x = param x := rfl


@[expose] def isoOfCommute (φ : W →ₗ[ZMod 2] W) (hinj : Function.Injective φ)
    (hT : ∀ x, T (φ x) = φ (T x)) (hPf : ∀ w ∈ W₀, Pf (φ w) = Pf w) :
    QuadraticMap.IsometryEquiv Q Q :=
  have hmem : ∀ w ∈ W₀, φ w ∈ W₀ := fun w hw => by
    rw [mem_W₀] at hw ⊢
    rw [hT, hw]
  ⟨LinearEquiv.ofInjectiveEndo (psiLin ∘ₗ φ ∘ₗ paramLin) (by
    intro x y hxy
    simp only [LinearMap.coe_comp, Function.comp_apply, paramLin_apply] at hxy
    have h := congrArg param hxy
    rw [param_psiLin (hmem _ (param_mem_W₀ x)), param_psiLin (hmem _ (param_mem_W₀ y))] at h
    rw [← psiLin_param x, ← psiLin_param y, hinj h]), fun x => by
    change Q (psiLin (φ (param x))) = Q x
    apply algebraMap_injective
    rw [← Pf_eq_Q (hmem _ (param_mem_W₀ x)), hPf _ (param_mem_W₀ x), Pf_param]⟩


@[expose] def ext2Lin (g : GL (Fin 4) K) : W →ₗ[ZMod 2] W :=
  (Matrix.mulVecLin (ext2GL g)).restrictScalars (ZMod 2)


@[expose] def suIso {g : GL (Fin 4) K} (hg : g ∈ SU) : QuadraticMap.IsometryEquiv Q Q :=
  isoOfCommute (ext2Lin g) (ext2GL_injective g) (T_ext2 hg) fun w _ => Pf_ext2GL hg w


abbrev linOf (g : GL (Fin 4) K) : V →ₗ[K] V := Matrix.mulVecLin (g : Matrix (Fin 4) (Fin 4) K)


end CFSG.LieType.Chevalley.C2E6Overlap
