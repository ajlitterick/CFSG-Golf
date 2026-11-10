module

public import CFSG.LieType.AlgebraicGroups.GLCoordDomain
public import CFSG.Blueprint.ChevalleyRoots
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv CFSG.Blueprint.Chevalley

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def glPoint (g : Matrix.GeneralLinearGroup ι k) : GLCoord k ι →ₐ[k] k :=
  GLCoord.lift k ι (g : Matrix ι ι k) ((g : Matrix ι ι k).det)⁻¹ (mul_inv_cancel₀ g.det_ne_zero)

@[simp] theorem glPoint_glEntry (g : Matrix.GeneralLinearGroup ι k) (i j : ι) :
    glPoint g (glEntry k ι i j) = (g : Matrix ι ι k) i j :=
  GLCoord.lift_glEntry k ι _ _ (mul_inv_cancel₀ g.det_ne_zero) i j

@[simp] theorem glPoint_glDetInv (g : Matrix.GeneralLinearGroup ι k) :
    glPoint g (glDetInv k ι) = ((g : Matrix ι ι k).det)⁻¹ :=
  GLCoord.lift_glDetInv k ι _ _ (mul_inv_cancel₀ g.det_ne_zero)

@[expose] def pointMatrix (φ : GLCoord k ι →ₐ[k] k) : Matrix ι ι k :=
  Matrix.of fun i j => φ (glEntry k ι i j)

theorem det_pointMatrix_mul (φ : GLCoord k ι →ₐ[k] k) :
    (pointMatrix φ).det * φ (glDetInv k ι) = 1 := by
  rw [pointMatrix, ← GLCoord.map_det, ← map_mul, det_glEntryMatrix_mul_glDetInv, map_one]

@[expose] def pointGL (φ : GLCoord k ι →ₐ[k] k) : Matrix.GeneralLinearGroup ι k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (pointMatrix φ)
    (left_ne_zero_of_mul_eq_one (det_pointMatrix_mul φ))

theorem convMul_glEntry (φ ψ : WithConv (GLCoord k ι →ₐ[k] k)) (i j : ι) :
    (φ * ψ).ofConv (glEntry k ι i j) =
      ∑ l, φ.ofConv (glEntry k ι i l) * ψ.ofConv (glEntry k ι l j) := by
  rw [AlgHom.convMul_apply, comul_glEntry, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]

theorem convMul_glDetInv (φ ψ : WithConv (GLCoord k ι →ₐ[k] k)) :
    (φ * ψ).ofConv (glDetInv k ι) = φ.ofConv (glDetInv k ι) * ψ.ofConv (glDetInv k ι) := by
  rw [AlgHom.convMul_apply, comul_glDetInv, Algebra.TensorProduct.lift_tmul]

@[expose] def glPointEquiv :
    Matrix.GeneralLinearGroup ι k ≃* WithConv (GLCoord k ι →ₐ[k] k) where
  toFun g := toConv (glPoint g)
  invFun φ := pointGL φ.ofConv
  left_inv g := Matrix.GeneralLinearGroup.ext fun i j => by
    simp [pointGL, pointMatrix]
  right_inv φ := by
    refine WithConv.ext (GLCoord.algHom_ext k ι (fun i j => ?_) ?_)
    · simp [pointGL, pointMatrix]
    · simp only [glPoint_glDetInv, pointGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact inv_eq_of_mul_eq_one_right (det_pointMatrix_mul φ.ofConv)
  map_mul' g h := by
    refine WithConv.ext (GLCoord.algHom_ext k ι (fun i j => ?_) ?_)
    · simp [convMul_glEntry, Matrix.mul_apply]
    · simp only [convMul_glDetInv, glPoint_glDetInv, Units.val_mul, Matrix.det_mul, mul_inv]

@[simp] theorem glPointEquiv_apply_glEntry (g : Matrix.GeneralLinearGroup ι k) (i j : ι) :
    (glPointEquiv g).ofConv (glEntry k ι i j) = (g : Matrix ι ι k) i j :=
  glPoint_glEntry g i j

@[simp] theorem glPointEquiv_apply_glDetInv (g : Matrix.GeneralLinearGroup ι k) :
    (glPointEquiv g).ofConv (glDetInv k ι) = ((g : Matrix ι ι k).det)⁻¹ :=
  glPoint_glDetInv g

@[simp] theorem glPointEquiv_symm_apply (φ : WithConv (GLCoord k ι →ₐ[k] k)) (i j : ι) :
    ((glPointEquiv.symm φ : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) i j =
      φ.ofConv (glEntry k ι i j) :=
  rfl

@[expose] def modGLEquivGL (τ : Tag) (K : Type*) [Field K] :
    ModGL τ K ≃* Matrix.GeneralLinearGroup (Label τ) K :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv
    (Finsupp.basisSingleOne : Module.Basis (Label τ) K (Label τ →₀ K))).toRingEquiv.toMulEquiv

@[simp] theorem modGLEquivGL_apply (τ : Tag) (K : Type*) [Field K]
    (g : ModGL τ K) (a b : Label τ) :
    (modGLEquivGL τ K g : Matrix (Label τ) (Label τ) K) a b =
      ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1)) a := by
  simp [modGLEquivGL, LinearMap.toMatrixAlgEquiv_apply]


end CFSG.LieType.AlgebraicGroups
