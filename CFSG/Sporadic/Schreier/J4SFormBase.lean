
module

public import CFSG.Sporadic.Schreier.J4SFormCheck

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def formF : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix 112 formRows

@[expose] def formUp : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix 112 formUpRows

@[expose] def jq : QuadraticForm (ZMod 2) (Fin 112 → ZMod 2) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' (ZMod 2) formUp)

theorem jq_apply (v : Fin 112 → ZMod 2) : jq v = v ⬝ᵥ (formUp *ᵥ v) := by
  rw [jq, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

theorem rowsMatrix_xorRows112 (X Y : Array ℕ) :
    rowsMatrix 112 (xorRows112 X Y) = rowsMatrix 112 X + rowsMatrix 112 Y := by
  ext i j
  rw [Matrix.add_apply, SmallF2.rowsMatrix_apply, SmallF2.rowsMatrix_apply,
    SmallF2.rowsMatrix_apply]
  unfold xorRows112
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply]

theorem formUp_add_transpose : formUp + formUpᵀ = formF := by
  rw [formUp, ← SmallF2.rowsMatrix_transposeRows, ← rowsMatrix_xorRows112, formUp_check.1]
  rfl

theorem polar_jq
    (u v : Fin 112 → ZMod 2) : QuadraticMap.polar jq u v = u ⬝ᵥ (formF *ᵥ v) := by
  have h : u ⬝ᵥ (formF *ᵥ v) = u ⬝ᵥ (formUp *ᵥ v) + v ⬝ᵥ (formUp *ᵥ u) := by
    rw [← formUp_add_transpose, Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm u (v ᵥ* formUp), ← Matrix.dotProduct_mulVec]
  rw [h, QuadraticMap.polar, jq_apply, jq_apply, jq_apply, Matrix.mulVec_add, dotProduct_add,
    add_dotProduct, add_dotProduct]
  abel

theorem formF_mul_inv : formF * rowsMatrix 112 formInvRows = 1 := by
  rw [formF, ← SmallF2.rowsMatrix_mulRows, formInv_check.1, SmallF2.rowsMatrix_idRows]

theorem jq_nondegenerate :
    (QuadraticMap.polarBilin jq).Nondegenerate := by
  have hinv := formF_mul_inv
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · have h : u ᵥ* formF = 0 := by
      funext j
      have h1 := hu (Pi.single j 1)
      rw [QuadraticMap.polarBilin_apply_apply, polar_jq, Matrix.dotProduct_mulVec,
        dotProduct_single, mul_one] at h1
      exact h1
    calc u = u ᵥ* (formF * rowsMatrix 112 formInvRows) := by rw [hinv, Matrix.vecMul_one]
      _ = (u ᵥ* formF) ᵥ* rowsMatrix 112 formInvRows := by rw [Matrix.vecMul_vecMul]
      _ = 0 := by rw [h, Matrix.zero_vecMul]
  · have h : formF *ᵥ v = 0 := by
      funext i
      have h1 := hv (Pi.single i 1)
      rw [QuadraticMap.polarBilin_apply_apply, polar_jq, single_dotProduct, one_mul] at h1
      exact h1
    have hinv' : rowsMatrix 112 formInvRows * formF = 1 := by
      rw [formF, ← SmallF2.rowsMatrix_mulRows, formInv_check.2, SmallF2.rowsMatrix_idRows]
    calc v = (rowsMatrix 112 formInvRows * formF) *ᵥ v := by rw [hinv', Matrix.one_mulVec]
      _ = rowsMatrix 112 formInvRows *ᵥ (formF *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero]

theorem dotProduct_add_transpose_mulVec (L : Matrix (Fin 112) (Fin 112) (ZMod 2))
    (v : Fin 112 → ZMod 2) : v ⬝ᵥ ((L + Lᵀ) *ᵥ v) = 0 := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose, dotProduct_comm v (v ᵥ* L),
    ← Matrix.dotProduct_mulVec]
  exact CharTwo.add_self_eq_zero _

theorem jq_vecMul_of_defect {G L : Matrix (Fin 112) (Fin 112) (ZMod 2)}
    (h : G * formUp * Gᵀ + formUp = L + Lᵀ) (v : Fin 112 → ZMod 2) : jq (v ᵥ* G) = jq v := by
  rw [jq_apply, jq_apply]
  have e : v ᵥ* G ⬝ᵥ (formUp *ᵥ (v ᵥ* G)) = v ⬝ᵥ ((G * formUp * Gᵀ) *ᵥ v) := by
    rw [← Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hG : G * formUp * Gᵀ = (L + Lᵀ) + formUp := by
    rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [e, hG, Matrix.add_mulVec, dotProduct_add, dotProduct_add_transpose_mulVec, zero_add]

theorem defectOK_spec {G : Array ℕ} (h : defectOK G = true) :
    formDefect G = xorRows112 (lowerRows (formDefect G))
      (transposeRows 112 (lowerRows (formDefect G))) := by
  unfold defectOK at h
  exact beq_iff_eq.1 h

theorem jq_vecMul_seed {G : Array ℕ}
    (h : formDefect G = xorRows112 (lowerRows (formDefect G))
      (transposeRows 112 (lowerRows (formDefect G)))) (v : Fin 112 → ZMod 2) :
    jq (v ᵥ* rowsMatrix 112 G) = jq v := by
  refine jq_vecMul_of_defect (L := rowsMatrix 112 (lowerRows (formDefect G))) ?_ v
  have h1 := congrArg (rowsMatrix 112) h
  rw [rowsMatrix_xorRows112, SmallF2.rowsMatrix_transposeRows] at h1
  rw [← h1, formDefect, rowsMatrix_xorRows112, SmallF2.rowsMatrix_mulRows,
    SmallF2.rowsMatrix_mulRows, SmallF2.rowsMatrix_transposeRows]
  rfl


end CFSG.Sporadic.J4Schreier
