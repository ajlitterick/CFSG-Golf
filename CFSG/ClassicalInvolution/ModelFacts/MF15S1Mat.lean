module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner
public import CFSG.RankThree.PartOne.LIT.CongruenceFive
public import CFSG.ClassicalInvolution.ModelFacts.MF15Sq
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open Matrix Module CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄₃" => Matrix (Fin 3) (Fin 3) F

@[expose] def rotJ : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩


theorem conj_comm_matrix {n : Type*} [Fintype n] [DecidableEq n] {B P Q g M : Matrix n n F}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hBP : B * P = P * M) (hMg : M * g = g * M) :
    B * (P * g * Q) = P * g * Q * B := by
  have hBQ : Q * B = M * Q := by
    calc Q * B = Q * B * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = Q * (B * P) * Q := by simp only [Matrix.mul_assoc]
      _ = M * Q := by rw [hBP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  calc B * (P * g * Q) = (B * P) * g * Q := by simp only [Matrix.mul_assoc]
    _ = P * (M * g) * Q := by rw [hBP]; simp only [Matrix.mul_assoc]
    _ = P * (g * M) * Q := by rw [hMg]
    _ = P * g * (M * Q) := by simp only [Matrix.mul_assoc]
    _ = P * g * Q * B := by rw [← hBQ]; simp only [Matrix.mul_assoc]

theorem conj_fixed_matrix {n : Type*} [Fintype n] [DecidableEq n]
    {B Bi P Q g M : Matrix n n F} (hBBi : B * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hBP : B * P = P * M) (hMg : M * g = g * M) : B * (P * g * Q) * Bi = P * g * Q := by
  rw [conj_comm_matrix hPQ hQP hBP hMg, Matrix.mul_assoc _ B, hBBi, Matrix.mul_one]

theorem slConj_fixed_of_comm (B P : GL (Fin 3) F) (g : SL(3, F)) (M : 𝕄₃)
    (hBP : (B : 𝕄₃) * P = (P : 𝕄₃) * M) (hMg : M * (g : 𝕄₃) = (g : 𝕄₃) * M) :
    slConjugation 3 F B (slConjugation 3 F P g) = slConjugation 3 F P g := by
  apply Subtype.ext
  rw [slConjugation_matrix, slConjugation_matrix]
  exact conj_fixed_matrix (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hBP hMg

theorem exists_sl_conj_block (P : GL (Fin 3) F) :
    ∃ k : SL(3, F), ∀ X : SL(2, F), k * blockSL F 3 2 0 (by norm_num) X * k⁻¹ =
      slConjugation 3 F P (blockSL F 3 2 0 (by norm_num) X) := by
  set d : F := (P : 𝕄₃).det with hd
  have hd0 : d ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det P).isUnit
    simpa [hd] using this
  let D : 𝕄₃ := !![1, 0, 0; 0, 1, 0; 0, 0, d⁻¹]
  have hK : ((P : 𝕄₃) * D).det = 1 := by
    rw [det_mul, ← hd]
    simp [D, det_fin_three, hd0]
  obtain ⟨k, hk⟩ : ∃ k : SL(3, F), (k : 𝕄₃) = (P : 𝕄₃) * D := ⟨⟨_, hK⟩, rfl⟩
  refine ⟨k, fun X => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, slConjugation_matrix,
    hk]
  have hPP : ((P⁻¹ : GL (Fin 3) F) : 𝕄₃) * (P : 𝕄₃) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDB : D * ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) =
      ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) * D := by
    rw [coe_blockSL_three_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_three]
  calc (P : 𝕄₃) * D * ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃)
      = (P : 𝕄₃) * (((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) * D) := by
        rw [Matrix.mul_assoc, hDB]
    _ = (P : 𝕄₃) * ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) *
          (((P⁻¹ : GL (Fin 3) F) : 𝕄₃) * (P : 𝕄₃)) * D := by
        rw [hPP, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_sq_mul_eq {u v : F} (hv : v ≠ 0) (h : IsSquare (u * v)) :
    ∃ s : F, s * s * v = u := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r / v, ?_⟩
  field_simp
  linear_combination hr.symm


end CFSG.ClassicalInvolution.ModelFacts.MF15
